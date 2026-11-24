-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Score

@[expose] public section

/-! # What the thread layer exports for the output accumulator

The correction thread of row `ρ` (warp `8 + ρ / 32`) of each CTA handles its row of both stages'
output accumulators `O` (`InO st`). For each stage it arrives on the leader's P-ready object once
before its first item (credit 0), once after each rescale and once after each final pass of an item
(credits `1, 2, …`; `pArr` counts them). The rescale of credit `q` (between the PV MMAs of tiles
`q - 1` and `q`, when the warp's ballot is nonzero) loads each 16-column chunk of the row
(`tcgen05.ld`, with the implicit `tcgen05.wait::ld` at the next index), multiplies it by `α` and
stores it back (`tcgen05.st`) before loading the next chunk; a `tcgen05.wait::st` follows the
stores, before the arrival. The final pass of credit `q` loads the row and stores nothing to
Tensor Memory. Every load or store of credit `q` comes after the arrival of credit `q - 1`.

A thread's trace may stop at any event: the `wait::ld` after a load is stated for a trace that
goes on past the load, the `wait::st` after a store before every later event of the thread that
is neither a `tcgen05` event nor undefined behaviour (`NonTcAfter`).

The fields are event-level facts of single threads from the correction's run invariant
(`Correction.Counts`) and its sites' Tensor Memory addresses. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The thread layer's facts for the output accumulator. -/
structure OAccFacts (L : Launch) (X : Execution) : Prop where
  /-- A correction load of credit `q ≥ 1` reads its row of one stage's accumulator; the implicit
  `wait::ld` is the thread's next event, if it has one. -/
  corr_ld : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → X.TLd (h, i) a vals .s32x32b → ∃ st < 2,
      (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧
      (i + 1 < (X.tr h).length → ∃ pc, X.get (h, i + 1) = some ⟨pc, .tc .waitLd⟩) ∧
      1 ≤ pArr L X h st i
  /-- A correction store of credit `q ≥ 1` writes its row of one stage's accumulator, after a
  load of the same credit; every later event of the thread that is not a `tcgen05` event comes
  after a `wait::st` of the same credit that follows the store. -/
  corr_st : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → X.TSt (h, i) a vals .s32x32b → ∃ st < 2,
      (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧ 1 ≤ pArr L X h st i ∧
      (∃ i' a' vals', i' < i ∧ X.TLd (h, i') a' vals' .s32x32b ∧
        (∀ j < vals'.length, InO st (tcDataCell32 L h a' j)) ∧ pArr L X h st i' = pArr L X h st i) ∧
      ∀ e, NonTcAfter X h i e →
        ∃ w pc, i < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
          pArr L X h st w = pArr L X h st i
  /-- A correction load of a cell comes before the store of the cell of the same credit. -/
  corr_ld_st : ∀ {h i i' a a' j j' st : Nat} {vals vals' : List Value}, h < L.threads →
    8 ≤ warpOf L h → warpOf L h < 12 → X.TLd (h, i) a vals .s32x32b →
    X.TSt (h, i') a' vals' .s32x32b →
    j < vals.length → j' < vals'.length → tcDataCell32 L h a j = tcDataCell32 L h a' j' →
    InO st (tcDataCell32 L h a j) → pArr L X h st i = pArr L X h st i' → i < i'
  /-- A correction thread stores each cell once per credit. -/
  corr_st_one : ∀ {h i i' a a' j j' st : Nat} {vals vals' : List Value}, h < L.threads →
    8 ≤ warpOf L h → warpOf L h < 12 → X.TSt (h, i) a vals .s32x32b →
    X.TSt (h, i') a' vals' .s32x32b →
    j < vals.length → j' < vals'.length → tcDataCell32 L h a j = tcDataCell32 L h a' j' →
    InO st (tcDataCell32 L h a j) → pArr L X h st i = pArr L X h st i' → i = i'

/-- Stage `st`'s O-full object in CTA `c` (the MMA thread's commit after the PV MMAs of an item,
multicast to both CTAs of the pair; polled by the correction threads before the final pass). -/
def oFullBar (L : Launch) (c st : Nat) : Loc := ⟨.shared, c, L.sharedBase + (192 + 8 * st)⟩

theorem oFullBar_eq (L : Launch) (c : Nat) (st : Fin 2) :
    oFullBar L c st = FBar.loc L c (.oFull st) := rfl

/-- The thread layer's facts for the O-full objects as mbarrier objects: only the MMA thread's
commits arrive on them, and a poll of one is a correction thread's of its CTA, with the parity of
its earlier successful polls of the object; a successful one acquires at cluster scope. A commit
notifying stage `st`'s object of CTA `c` is the elected lane's of warp 12 of `c`'s pair leader
and names the stage's object of its own CTA (`o_commit`, as `SFullFacts.s_commit`). -/
structure OFullFacts (L : Launch) (X : Execution) : Prop where
  o_arrive : ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, st < 2 →
    X.get (g, i) ≠ some ⟨pc, .arrive (oFullBar L c st) tx cnt rel sc⟩
  o_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ oFullBar L c st
  o_poll : ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads → st < 2 →
    X.get (g, i) = some ⟨pc, .wait (oFullBar L c st) p ok acq sc⟩ →
      ctaOf L g = c ∧ 8 ≤ warpOf L g ∧ warpOf L g < 12 ∧
        p % 2 = okPolls (oFullBar L c st) ((X.tr g).take i) % 2 ∧
        (ok = true → acq = true ∧ sc = .cluster)
  o_commit : ∀ {g k pc c st : Nat} {sp : TcCommit.Spec} {r : Fin 16}, g < L.threads → st < 2 →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (oFullBar L c st) →
      warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
        sp.mbar = oFullBar L (ctaOf L g) st

end
end PTX.Kernels.FlashAttn4Fwd.Proof
