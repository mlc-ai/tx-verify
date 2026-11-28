-- SPDX-License-Identifier: Apache-2.0
-- iface: W0Payloads producer=W1 status=stated domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # What warpgroup 0's reads deliver: the typing of the words

`W0Payloads P L X`: every event of a lane of warps 0 to 3 that delivers a word warpgroup 0 reads
carries a word of the right TYPE, and the one fact about the peer lane's statistics the epilogue
needs. It is event by event, in the vocabulary of the trace (`w0Words`, `Rd`, `W0Fin`), and is the
hypothesis of `wg0_noUb` (`Wg0/Export/NoUb.lean`): the strict steps of warpgroup 0's data machine
need these words to be numbers (the conditions of the arithmetic runs), and the words come from
other lanes' stores and from the Tensor Memory loads.

* the score loads: the high half's 32 words are clean finite numbers (pcs 278, 285), the low
  half's 32 words are score halves (pcs 280, 283);
* the validity word (pc 289) is a 32-bit word; a peer element (pcs `477 + 5 k`) has two half
  words that read as finite numbers; the peer's row maximum (pc 572) is a clean finite number or
  the pattern of negative infinity;
* the length loads (pcs 168, 181) read bytes that rebuild to a word;
* the sink load (pc 156) reads the bits of a finite `f32`;
* the peer's row-sum word (pc 1157) reads as `p` with `0 ≤ p`, and `p = 0` while the lane's
  carried maximum is still `-inf` (the partner stored its own sum, which is zero then);
* the accumulator loads (`w0OPcs`) are 64 words that read as numbers.

The scale `0 < P.scale` is a parameter fact, not a payload. A word is typed by how it READS
(`Rd`, `W0Fin`), never by its constructor. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- **The typing of the word event `e` delivers**, after the events `l` of its lane (the scale
`sc` fixes the carried maximum the row-sum field speaks of). -/
def W0EvPayload (sc : ℝ) (l : List Event) (e : Event) : Prop :=
  (∀ vals, w0TcVals e = some vals → (e.pc = 278 ∨ e.pc = 285) →
    vals.length = 32 ∧ ∀ c < 32,
      PTX.Flow.Clean (vals.getD c (.pred false)) ∧ W0Fin (vals.getD c (.pred false))) ∧
  (∀ vals, w0TcVals e = some vals → (e.pc = 280 ∨ e.pc = 283) →
    vals.length = 32 ∧ ∀ c < 32,
      Kernels.FlashMlaSparseDecodeH64.Assumptions.scoreHalf (vals.getD c (.pred false))) ∧
  (∀ x bs, e.kind = .nc x bs → (e.pc = 168 ∨ e.pc = 181) → ∃ v, rebuild 3 bs = .ok v) ∧
  (∀ x bs, e.kind = .rd x bs → e.pc = 289 →
    ∃ n < 2 ^ 32, rebuild 3 bs = .ok (.bits 32 (BitVec.ofNat 64 n))) ∧
  (∀ x bs, e.kind = .rd x bs → (∃ k < 8, e.pc = 477 + 5 * k) →
    ∃ v, rebuild 3 bs = .ok v ∧ W0Fin (splitValue 64 v).1 ∧ W0Fin (splitValue 64 v).2) ∧
  (∀ x bs, e.kind = .rd x bs → e.pc = 572 →
    ∃ v, rebuild 3 bs = .ok v ∧ PTX.Flow.Clean v ∧ (W0Fin v ∨ v = w0NegInf)) ∧
  (∀ x bs, e.kind = .nc x bs → e.pc = 156 →
    ∃ (bits : Nat) (q : ℚ), bits < 2 ^ 32 ∧ f32Value bits = some q ∧
      rebuild 3 bs = .ok (b32 bits)) ∧
  (∀ x bs, e.kind = .rd x bs → e.pc = 1157 →
    ∃ (v : Value) (p : ℝ), rebuild 3 bs = .ok v ∧ 0 ≤ p ∧ Rd v p ∧
      (w0MxCarry sc (w0Fin l).1 = ⊥ → p = 0)) ∧
  (∀ vals, w0TcVals e = some vals → e.pc ∈ w0OPcs →
    vals.length = 64 ∧ ∃ O : Nat → ℝ, ∀ i < 64, Rd (vals.getD i (.pred false)) (O i))

/-- **The payloads of warpgroup 0**: every event of a lane of warps 0 to 3 (the startup's, the
warpgroup's) carries the typed words, given the events of its lane before it. -/
def W0Payloads (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k e, g < L.threads → MbarRow.warp L g < 4 → X.get (g, k) = some e →
    W0EvPayload P.scale ((X.tr g).take k) e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
