// Pump.fun Bot Sprint entry: a deterministic momentum bot for agent-fun/replay/v2.
//
// Strategy in one paragraph: watch every curve's recorded tape. Buy at most
// once per curve, a small fixed stake, into curves that are past their launch
// minutes and show real, broad, accelerating buy pressure: net SOL inflow
// over a rolling window, several distinct buyers, no single wallet
// dominating, inflow still positive in the last few slots, price up but not
// vertical and sitting near its window high. Add once, half size, into a
// position that is already up at least 10% (pyramid into strength only).
// Sell the whole position on the first of a take-profit, a stop loss, a
// trailing stop once the run is armed, or a time limit. If completed round
// trips ever lag the pace the guardrail needs (20 coins with a round trip of
// at least 0.01 SOL), fall back to tiny probe trades on the most liquid
// active curves just to bank round trips cheaply.
//
// This is a line-for-line TypeScript port of the audited Python strategy:
// same constants, same decision order, same integer arithmetic. Python's
// arbitrary-precision ints become BigInt here (u64 values arrive as decimal
// strings), and Python's floor division is reproduced explicitly where a
// numerator can be negative. Like the kit's own hold-cash baseline, the file
// uses no TypeScript-only syntax beyond what Node strips natively, so it
// also passes a plain `node --check`.
//
// Determinism: no clock, no randomness, no environment reads. All decisions
// are integer arithmetic over the batch stream; iteration is over
// insertion-ordered Maps and explicitly sorted candidate lists, so the two
// graded executions produce byte-identical replies.
//
// Run by the grader as `node /bot/main.ts`; the vendored shim in
// vendor/makefun-bot.ts owns the wire protocol.

import { runBot, LAMPORTS_PER_SOL, BPS } from './vendor/makefun-bot.ts';

const SOL = LAMPORTS_PER_SOL;

// ---------------------------------------------------------------------------
// Parameters (lamports, basis points and slots only; no floats anywhere).
// ---------------------------------------------------------------------------

// Entry tape window and shape filters.
const WINDOW_SLOTS = 240; // rolling tape window for entry statistics
const MIN_AGE_SLOTS = 120; // skip the launch minutes of a curve
const MIN_REAL_QUOTE = 1n * SOL; // curve must hold at least 1 SOL of real quote
const MAX_REAL_QUOTE = 80n * SOL; // ... and not be nearly graduated already
const MIN_NET_INFLOW = 2n * SOL; // net buy-minus-sell quote over the window
const MIN_BUY_TRADES = 8;
const MIN_DISTINCT_BUYERS = 5;
const MAX_BUYER_SHARE_BPS = 6500; // one wallet may not dominate window buy flow
const MIN_PRICE_UP_BPS = 500; // price at least +5% across the window
const MAX_PRICE_UP_BPS = 7000; // ... but not +70%: do not chase a vertical top
const NEAR_HIGH_PCT = 92; // price at least 92% of the window's best price
const RECENT_WINDOW_SLOTS = 45; // the freshest slice of the tape ...
const RECENT_MIN_NET = (3n * SOL) / 10n; // ... must still be net buying at least this
const BURST_SLOTS = 30; // price may not be up more than ...
const BURST_MAX_PCT = 135; // ... 35% over the last 30 slots (a blow-off)

// Sizing.
const STAKE_MAX = 100_000_000n; // 0.10 SOL per position at most
const ADD_ARM_BPS = 1000; // pyramid add once value is +10% over cost
const ADD_SHARE = 2n; // the add is STAKE_MAX / ADD_SHARE at most
const STAKE_MIN = 12_000_000n; // below a 0.012 SOL cap the trade is not worth it
const BUY_SLIPPAGE_BPS = 1500;
const SELL_SLIPPAGE_BPS = 10_000; // exits always fill

// Exits (values are the position's net sell value versus its cost basis).
const TAKE_PROFIT_BPS = 2000; // +20%
const STOP_LOSS_BPS = 1200; // -12%
const TRAIL_ARM_BPS = 3000; // trailing stop arms at +30%
const TRAIL_GIVEBACK_BPS = 1500; // ... and fires 15% under the peak value
const TIME_STOP_SLOTS = 1200; // no position rides longer than this

// Guardrail probes: tiny round trips on liquid curves when the pace lags.
const PROBE_STAKE = 12_000_000n; // 0.012 SOL, just over the 0.01 SOL trip floor
const PROBE_MIN_REAL_QUOTE = 3n * SOL;
const PROBE_TAKE_PROFIT_BPS = 500;
const PROBE_STOP_LOSS_BPS = 500;
const PROBE_TIME_STOP_SLOTS = 180;
const ROUND_TRIP_FLOOR = 10_000_000n; // the guardrail's min buy per counted trip
const TRIPS_WANTED = 20;
const WINDOW_SECONDS = 21_600; // the final window is 6 hours of block time

const TAPE_CAP = 900; // per-mint tape entries kept (most recent)

/** Python `//` on possibly-negative numerators: floor division (divisor > 0). */
function floorDiv(a, b) {
  const q = a / b;
  return a % b !== 0n && a < 0n ? q - 1n : q;
}

function minBig(a, b) {
  return a < b ? a : b;
}

// One tape entry: { slot, isBuy, quote, user, vq, vt } with quote/vq/vt as
// BigInt lamport/reserve amounts and slot as a plain number.
class Tape {
  constructor(createdSlot) {
    this.createdSlot = createdSlot; // number, or null when first seen via a trade
    this.trades = [];
    this.lastSlot = -1;
  }

  add(slot, isBuy, quote, user, vq, vt) {
    this.trades.push({ slot, isBuy, quote, user, vq, vt });
    this.lastSlot = slot;
    const cutoff = slot - WINDOW_SLOTS;
    while (this.trades.length > 0 && this.trades[0].slot < cutoff) {
      this.trades.shift();
    }
    while (this.trades.length > TAPE_CAP) {
      this.trades.shift();
    }
  }
}

class Position {
  constructor(mint, entrySlot, probe) {
    this.mint = mint;
    this.entrySlot = entrySlot;
    this.peakBps = 0n; // best value-versus-cost seen, in bps over cost
    this.exiting = false; // an exit was decided; keep selling until flat
    this.probe = probe;
    this.added = false; // the single pyramid add has been sent
  }
}

class Bot {
  constructor(hello) {
    this.caps = hello.caps;
    this.txFee = BigInt(hello.fees.base_fee_lamports) + BigInt(hello.fees.priority_fee_lamports);
    this.feeBps = BigInt(hello.fees.protocol_bps_fallback) + BigInt(hello.fees.creator_bps_fallback);
    this.tapes = new Map(); // mint -> Tape, in first-seen order
    this.positions = new Map(); // mint -> Position, in open order
    this.pendingBuys = new Map(); // mint -> true while a buy is in flight
    this.entered = new Set(); // mints already entered once this run
    this.probeMints = new Set(); // mints entered as probes (only membership)
    this.bought = new Map(); // mint -> total filled buy quote (for trips)
    this.tripsDone = new Set(); // mints whose position opened and closed
    this.firstBlockTime = null;
    this.lastBlockTime = null;
  }

  // -- tape ---------------------------------------------------------------

  ingest(batch) {
    const traded = [];
    for (const e of batch.events) {
      const bt = e.block_time;
      if (bt !== null && bt !== undefined) {
        if (this.firstBlockTime === null) {
          this.firstBlockTime = bt;
        }
        this.lastBlockTime = bt;
      }
      const kind = e.event;
      const mint = e.mint;
      if (kind === 'CreateEvent') {
        if (!this.tapes.has(mint)) {
          this.tapes.set(mint, new Tape(e.slot));
        }
      } else if (kind === 'TradeEvent') {
        let tape = this.tapes.get(mint);
        if (tape === undefined) {
          tape = new Tape(null);
          this.tapes.set(mint, tape);
        }
        tape.add(
          e.slot,
          Boolean(e.is_buy),
          BigInt(e.quote_amount),
          e.user,
          BigInt(e.virtual_quote_reserves),
          BigInt(e.virtual_token_reserves),
        );
        traded.push(mint);
      }
    }
    return traded;
  }

  // -- valuation ----------------------------------------------------------

  sellValue(curve, tokens) {
    // Net lamports a full sell returns now, curve fees deducted.
    if (tokens <= 0n || curve.virtual_token_reserves <= 0n) {
      return 0n;
    }
    const q = (tokens * curve.virtual_quote_reserves) / (curve.virtual_token_reserves + tokens);
    // Ceil of q * feeBps / BPS, as the program charges (Python: -(-q * fee_bps // BPS);
    // q and feeBps are non-negative here, so the direct ceil form is exact).
    const fee = (q * this.feeBps + BPS - 1n) / BPS;
    return q - fee;
  }

  // -- round-trip bookkeeping ---------------------------------------------

  syncPositions(state) {
    const held = state.positions;
    for (const mint of [...this.positions.keys()]) {
      if (!held.has(mint)) {
        if ((this.bought.get(mint) ?? 0n) >= ROUND_TRIP_FLOOR) {
          this.tripsDone.add(mint);
        }
        this.positions.delete(mint);
        this.probeMints.delete(mint);
      }
    }
    for (const mint of held.keys()) {
      if (!this.positions.has(mint)) {
        this.positions.set(mint, new Position(mint, state.slot, this.probeMints.has(mint)));
      }
    }
  }

  noteFills(batch) {
    for (const f of batch.fills) {
      if (f.client_id.startsWith('_')) {
        continue; // harness closes: the position sync sees their effect
      }
      if (f.side !== 'buy') {
        continue;
      }
      // Any resolution (filled, rejected or failed) ends the flight.
      this.pendingBuys.delete(f.mint);
      if (f.status === 'filled') {
        const mint = f.mint;
        this.bought.set(mint, (this.bought.get(mint) ?? 0n) + BigInt(f.quote_lamports));
      }
    }
  }

  // -- entries --------------------------------------------------------------

  entrySignal(state, mint) {
    // Stake in lamports if the curve passes every entry filter, else 0n.
    const curve = state.curves.get(mint);
    const tape = this.tapes.get(mint);
    if (curve === undefined || tape === undefined || curve.complete) {
      return 0n;
    }
    if (tape.createdSlot === null || state.slot - tape.createdSlot < MIN_AGE_SLOTS) {
      return 0n;
    }
    const rq = curve.real_quote_reserves;
    if (rq < MIN_REAL_QUOTE || rq > MAX_REAL_QUOTE) {
      return 0n;
    }
    const trades = tape.trades;
    if (trades.length < MIN_BUY_TRADES) {
      return 0n;
    }
    const midSlot = state.slot - Math.floor(WINDOW_SLOTS / 2);
    let buyQ = 0n;
    let sellQ = 0n;
    let oldNet = 0n;
    let newNet = 0n;
    const buyers = new Map();
    let nBuys = 0;
    for (const t of trades) {
      if (t.isBuy) {
        buyQ += t.quote;
        nBuys += 1;
        buyers.set(t.user, (buyers.get(t.user) ?? 0n) + t.quote);
        if (t.slot < midSlot) {
          oldNet += t.quote;
        } else {
          newNet += t.quote;
        }
      } else {
        sellQ += t.quote;
        if (t.slot < midSlot) {
          oldNet -= t.quote;
        } else {
          newNet -= t.quote;
        }
      }
    }
    const net = buyQ - sellQ;
    if (net < MIN_NET_INFLOW || nBuys < MIN_BUY_TRADES) {
      return 0n;
    }
    if (buyers.size < MIN_DISTINCT_BUYERS) {
      return 0n;
    }
    if (buyers.size > 0) {
      let maxBuyer = 0n;
      for (const v of buyers.values()) {
        if (v > maxBuyer) maxBuyer = v;
      }
      if (maxBuyer * BPS > buyQ * BigInt(MAX_BUYER_SHARE_BPS)) {
        return 0n;
      }
    }
    // The most recent slice of the tape must still be net buying, and
    // the price must not have gone vertical in the last few slots.
    let recentNet = 0n;
    let burstRef = null;
    for (const t of trades) {
      if (t.slot >= state.slot - RECENT_WINDOW_SLOTS) {
        recentNet += t.isBuy ? t.quote : -t.quote;
      }
      if (t.slot <= state.slot - BURST_SLOTS) {
        burstRef = { vq: t.vq, vt: t.vt };
      }
    }
    if (recentNet <= RECENT_MIN_NET) {
      return 0n;
    }
    if (burstRef !== null && burstRef.vq > 0n && burstRef.vt > 0n) {
      const last = trades[trades.length - 1];
      if (last.vq * burstRef.vt * 100n > burstRef.vq * last.vt * BigInt(BURST_MAX_PCT)) {
        return 0n;
      }
    }
    // Acceleration: the newer half must at least match the older half,
    // unless the older half was already a wash and the new one is strong.
    if (newNet < oldNet && !(oldNet <= 0n && newNet >= MIN_NET_INFLOW / 2n)) {
      return 0n;
    }
    // Near the window high: the best post-trade price on the tape,
    // kept as a (vq, vt) pair and compared by cross-multiplication.
    let hvq = trades[0].vq;
    let hvt = trades[0].vt;
    for (const t of trades) {
      if (t.vq * hvt > hvq * t.vt) {
        hvq = t.vq;
        hvt = t.vt;
      }
    }
    // Price change across the window, as an exact integer comparison.
    const vq0 = trades[0].vq;
    const vt0 = trades[0].vt;
    const vq1 = trades[trades.length - 1].vq;
    const vt1 = trades[trades.length - 1].vt;
    if (vq1 * hvt * 100n < hvq * vt1 * BigInt(NEAR_HIGH_PCT)) {
      return 0n;
    }
    if (vq0 <= 0n || vt0 <= 0n || vq1 <= 0n || vt1 <= 0n) {
      return 0n;
    }
    // price_now / price_start = (vq1 * vt0) / (vq0 * vt1); bound the ratio.
    const lhs = vq1 * vt0 * BPS;
    const rhs = vq0 * vt1;
    if (lhs < rhs * (BPS + BigInt(MIN_PRICE_UP_BPS))) {
      return 0n;
    }
    if (lhs > rhs * (BPS + BigInt(MAX_PRICE_UP_BPS))) {
      return 0n;
    }
    const cap = state.maxBuyLamports(mint);
    if (cap < STAKE_MIN) {
      return 0n;
    }
    return minBig(STAKE_MAX, cap);
  }

  probeSignal(state, mint) {
    // A liquid, recently active curve for a guardrail probe buy.
    const curve = state.curves.get(mint);
    const tape = this.tapes.get(mint);
    if (curve === undefined || tape === undefined || curve.complete) {
      return false;
    }
    if (curve.real_quote_reserves < PROBE_MIN_REAL_QUOTE) {
      return false;
    }
    if (state.slot - tape.lastSlot > 90) {
      return false;
    }
    // Not in a clear slide over the tape window: price within -5%.
    if (tape.trades.length >= 2) {
      const vq0 = tape.trades[0].vq;
      const vt0 = tape.trades[0].vt;
      const vq1 = tape.trades[tape.trades.length - 1].vq;
      const vt1 = tape.trades[tape.trades.length - 1].vt;
      if (vq0 > 0n && vt0 > 0n && vq1 * vt0 * 100n < vq0 * vt1 * 95n) {
        return false;
      }
    }
    return state.maxBuyLamports(mint) >= PROBE_STAKE;
  }

  tripsTarget() {
    // Round trips that should be banked or in flight by now.
    if (this.firstBlockTime === null || this.lastBlockTime === null) {
      return 0;
    }
    const elapsed = this.lastBlockTime - this.firstBlockTime;
    if (elapsed < Math.floor(WINDOW_SECONDS / 4)) {
      return 0;
    }
    if (elapsed < Math.floor(WINDOW_SECONDS / 2)) {
      return 8;
    }
    if (elapsed < Math.floor((WINDOW_SECONDS * 3) / 4)) {
      return 13;
    }
    if (elapsed < Math.floor((WINDOW_SECONDS * 11) / 12)) {
      return 17;
    }
    return TRIPS_WANTED;
  }

  // -- the per-batch decision ------------------------------------------------

  onBatch(state, batch) {
    // Per batch, in order: settle fills, fold this slot's events into the
    // tapes, sync positions (banking round trips), then decide orders:
    // exits, the pyramid add, momentum entries, guardrail probes.
    this.noteFills(batch);
    const traded = this.ingest(batch);
    this.syncPositions(state);

    const orders = [];
    const maxOrders = this.caps.max_orders_per_batch;
    let free = state.freeCashLamports();
    let slots = this.caps.max_open_positions - state.committedPositionCount();

    // 1. Exits first: they free slots and never compete with entries.
    for (const [mint, pos] of this.positions) {
      if (orders.length >= maxOrders) {
        break;
      }
      const held = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (held === undefined || curve === undefined) {
        continue;
      }
      let sellPending = false;
      for (const p of state.pending.values()) {
        if (p.order.side === 'sell' && p.order.mint === mint) {
          sellPending = true;
          break;
        }
      }
      if (sellPending) {
        continue;
      }
      const value = this.sellValue(curve, held.token_amount);
      const cost = held.cost_lamports;
      if (cost <= 0n) {
        continue;
      }
      const gainBps = floorDiv((value - cost) * BPS, cost);
      if (gainBps > pos.peakBps) {
        pos.peakBps = gainBps;
      }
      const tp = pos.probe ? PROBE_TAKE_PROFIT_BPS : TAKE_PROFIT_BPS;
      const sl = pos.probe ? PROBE_STOP_LOSS_BPS : STOP_LOSS_BPS;
      const tstop = pos.probe ? PROBE_TIME_STOP_SLOTS : TIME_STOP_SLOTS;
      let exitNow = pos.exiting;
      if (gainBps >= BigInt(tp) || gainBps <= -BigInt(sl)) {
        exitNow = true;
      } else if (pos.peakBps >= BigInt(TRAIL_ARM_BPS) && gainBps <= pos.peakBps - BigInt(TRAIL_GIVEBACK_BPS)) {
        exitNow = true;
      } else if (state.slot - pos.entrySlot >= tstop) {
        exitNow = true;
      }
      if (exitNow) {
        pos.exiting = true;
        orders.push({
          side: 'sell',
          mint,
          token_amount: held.token_amount,
          max_slippage_bps: SELL_SLIPPAGE_BPS,
        });
        free -= this.txFee;
      }
    }

    // 1b. One pyramid add into a position that is working: value at
    // least +10% over cost and the tape still net-buying. The add is
    // sized by the size cap like any buy and joins the same round trip.
    for (const [mint, pos] of this.positions) {
      if (orders.length >= maxOrders) {
        break;
      }
      if (pos.probe || pos.added || pos.exiting) {
        continue;
      }
      const held = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (held === undefined || curve === undefined || this.pendingBuys.has(mint)) {
        continue;
      }
      const value = this.sellValue(curve, held.token_amount);
      if (held.cost_lamports <= 0n || (value - held.cost_lamports) * BPS < held.cost_lamports * BigInt(ADD_ARM_BPS)) {
        continue;
      }
      const add = minBig(STAKE_MAX / ADD_SHARE, state.maxBuyLamports(mint));
      if (add < STAKE_MIN || free < add + this.txFee) {
        continue;
      }
      orders.push({
        side: 'buy',
        mint,
        quote_lamports: add,
        max_slippage_bps: BUY_SLIPPAGE_BPS,
      });
      this.pendingBuys.set(mint, true);
      pos.added = true;
      free -= add + this.txFee;
    }

    // 2. Momentum entries on curves that traded in this batch.
    if (slots > 0 && orders.length < maxOrders) {
      const scored = [];
      const seen = new Set();
      for (const mint of traded) {
        if (seen.has(mint) || this.positions.has(mint) || this.pendingBuys.has(mint) || this.entered.has(mint)) {
          continue;
        }
        seen.add(mint);
        const stake = this.entrySignal(state, mint);
        if (stake > 0n) {
          const tape = this.tapes.get(mint);
          let net = 0n;
          for (const t of tape.trades) {
            net += t.isBuy ? t.quote : -t.quote;
          }
          scored.push({ negNet: -net, mint, stake });
        }
      }
      scored.sort((a, b) => {
        if (a.negNet !== b.negNet) return a.negNet < b.negNet ? -1 : 1;
        if (a.mint !== b.mint) return a.mint < b.mint ? -1 : 1;
        if (a.stake !== b.stake) return a.stake < b.stake ? -1 : 1;
        return 0;
      });
      for (const s of scored) {
        if (slots <= 0 || orders.length >= maxOrders) {
          break;
        }
        if (free < s.stake + this.txFee) {
          continue;
        }
        orders.push({
          side: 'buy',
          mint: s.mint,
          quote_lamports: s.stake,
          max_slippage_bps: BUY_SLIPPAGE_BPS,
        });
        this.pendingBuys.set(s.mint, true);
        this.entered.add(s.mint);
        free -= s.stake + this.txFee;
        slots -= 1;
      }
    }

    // 3. Guardrail probes when the round-trip pace lags.
    if (slots > 0 && orders.length < maxOrders) {
      const banked = this.tripsDone.size + this.positions.size + this.pendingBuys.size;
      if (banked < this.tripsTarget()) {
        let best = null;
        for (const [mint] of this.tapes) {
          if (this.positions.has(mint) || this.pendingBuys.has(mint) || this.tripsDone.has(mint)) {
            continue;
          }
          if (!this.probeSignal(state, mint)) {
            continue;
          }
          const rq = state.curves.get(mint).real_quote_reserves;
          const cand = { negRq: -rq, mint };
          if (
            best === null ||
            cand.negRq < best.negRq ||
            (cand.negRq === best.negRq && cand.mint < best.mint)
          ) {
            best = cand;
          }
        }
        if (best !== null && free >= PROBE_STAKE + this.txFee) {
          const mint = best.mint;
          orders.push({
            side: 'buy',
            mint,
            quote_lamports: PROBE_STAKE,
            max_slippage_bps: BUY_SLIPPAGE_BPS,
          });
          this.pendingBuys.set(mint, true);
          this.probeMints.add(mint);
        }
      }
    }

    return orders;
  }
}

let bot = null;

await runBot({
  onHello(state) {
    bot = new Bot(state.hello);
  },
  onBatch(state, batch) {
    return bot.onBatch(state, batch);
  },
});
