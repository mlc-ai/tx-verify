-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Obj
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Full
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias hand-offs

Stage `st`'s bias full barrier `320 + 8 st` is completed by one lane of warp 14 (`tmaFull`: an
expect-tx arrival and two tensor copies per use) and its empty barrier `336 + 8 st` by the unit
arrivals of lane 0 of the stage's four softmax warps (`biasFreeHist`), each after one more poll of
the full barrier than its earlier arrivals. The items of use `t` follow `t + 1` polls of the empty
barrier (`tmaFull_pol`), whose parities are `ld_tma_empty_par`. So the stage is a `MbarRing.KRing`
with four consumers (`biasRing`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Frame (MbarOf)
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The full and the empty bias barrier of stage `st`. -/
abbrev bF (L : Launch) (g : Nat) (st : Fin 2) : Loc := obj L g (320 + 8 * st.val)
abbrev bE (L : Launch) (g : Nat) (st : Fin 2) : Loc := obj L g (336 + 8 * st.val)

theorem b_tmaOff (st : Fin 2) : LdTmaOff (320 + 8 * st.val) := by
  have := st.isLt
  unfold LdTmaOff
  omega

theorem bE_eq (L : Launch) (g : Nat) (st : Fin 2) :
    obj L g (320 + 8 * st.val + 16) = bE L g st := by
  simp only [bE]
  congr 1
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A bias stage as a ring of kinds.** -/
def biasRing (hB : TmaBytes X) (g : Nat) (st : Fin 2) : KRing L kernel X 1 4 3 :=
  have o := tmaFull hp hX hFw hB g (b_tmaOff st)
  have N := biasFreeHist hp hX hFw g st
  have hparF : ∀ {h k pc par : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait (bF L g st) par true acq sc⟩ →
      par % 2 = (okPolls (bF L g st) ((X.tr h).take k) + 0) % 2 := by
    intro h k pc par acq sc he
    obtain ⟨-, hu⟩ := bias_use hp hX hFw st he rfl (fun _ h => by cases h)
    rcases hu with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, _, hk, _⟩
    · simp only [Kind.wait.injEq] at hk
      simp only [bF]
      omega
    · cases hk
    · cases hk
  have hparE : ∀ {h k pc par : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait (bE L g st) par true acq sc⟩ →
      par % 2 = (okPolls (bE L g st) ((X.tr h).take k) + 1) % 2 := by
    intro h k pc par acq sc he
    rcases biasFree_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨⟨hc, hw⟩, _⟩ | ⟨hk, _⟩
    · rw [← bE_eq] at he ⊢
      rw [← obj_cta hc] at he ⊢
      exact (ld_tma_empty_par hp hX hFw hw (b_tmaOff st) he).2
    · cases hk
  { F := bF L g st
    E := bE L g st
    prod := fun _ => tmaLane L X g
    cons := biasLane L (g / L.block) st.val
    ownF := fun _ => 0
    opF := TmaUnits.op X (bF L g st) (tmaLane L X g) 2
    itF := TmaUnits.it X (bF L g st) (tmaLane L X g) 2
    cm := Unit.it X (bE L g st) (biasLane L (g / L.block) st.val)
    note := fun a t => .thread (Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) a t)
    SF := TmaUnits.S X (bF L g st) (tmaLane L X g) 2 16384
    SE := Unit.S X (bE L g st) (biasLane L (g / L.block) st.val)
    cover := fun a => ⟨0, Subsingleton.elim _ _⟩
    cF := o.counted
    cE :=
      { record := fun x hx => by
          obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := N.S_rec hx
          exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
        init := ⟨4, N.init⟩
        noInval := N.noInval }
    spins := poll_spin hX
    parF := fun _ _ _ _ _ _ he => hparF he
    parE := fun _ _ _ _ _ _ he => hparE he
    fullF := fun _ j hj => o.card_phase hX (by decide) (by decide) (δ := 0) (Nat.zero_le _)
      (MbarRing.Poll.alternates hX (o.counted.pclean hX) fun _ _ _ _ _ he => hparF he)
      (Nat.zero_le _) hj
    fullE := fun _ n hn hj => N.card_phase hX (δ := 1) le_rfl
      (MbarRing.Poll.alternates hX (N.pclean hX) fun _ _ _ _ _ he => hparE he) hn hj
    polF := fun x hx => by
      obtain ⟨i, h1, h2, h3⟩ := tmaFull_pol hp hX hFw hB g (b_tmaOff st) hx
      rw [bE_eq] at h3
      exact ⟨i, h1, h2, h3⟩
    polE := fun y hy => by
      obtain ⟨-, ⟨pc, sc, hget⟩, hcnt⟩ := N.S_rec hy
      refine ⟨_, rfl, len_of_get hget, ?_⟩
      rcases biasFree_use hp hX hFw st (h := biasLane L (g / L.block) st.val y.1) hget rfl
        (fun _ h => by cases h) with ⟨_, _, _, hk⟩ | ⟨-, -, h1⟩
      · cases hk
      · exact (h1.trans (congrArg (· + 1) hcnt)).ge
    issueF := fun _ hx => o.issue hX hx
    issueE := fun _ _ => .refl }

/-- **The bias hand-offs** of stage `st`, between the lane `y` of warp 14 that won its elections and
lane 0 of the stage's softmax warps: a poll of the full barrier with `u` earlier ones observes `y`'s
two copies `2 u`, `2 u + 1` on it, and `y`'s poll of the empty barrier with `u + 1` earlier ones
the release of every warp with `u` earlier ones: a stage's next copies follow them. -/
theorem biasHandoff (hB : TmaBytes X) (g : Nat) (st : Fin 2) :
    (∀ {b : Fin 4} {j pc par u : Nat} {acq : Bool} {sc : MbarScope},
      X.get (biasLane L (g / L.block) st.val b, j) =
        some ⟨pc, .wait (bF L g st) par true acq sc⟩ →
      okPolls (bF L g st) ((X.tr (biasLane L (g / L.block) st.val b)).take j) = u → ∀ a : Fin 2,
        ∃ i pci al sp, X.get (tmaLane L X g, i) = some ⟨pci, .tensorIssue al sp⟩ ∧
          sp.mbar = bF L g st ∧
          ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) = 2 * u + a.val ∧
          u + 1 ≤ okPolls (bE L g st) ((X.tr (tmaLane L X g)).take i) ∧
          WaitObserves X (.async (tmaLane L X g, i) (.notify .load))
            (biasLane L (g / L.block) st.val b, j) (bF L g st) acq sc) ∧
    ∀ {j pc par u : Nat} {acq : Bool} {sc : MbarScope},
      X.get (tmaLane L X g, j) = some ⟨pc, .wait (bE L g st) par true acq sc⟩ →
      okPolls (bE L g st) ((X.tr (tmaLane L X g)).take j) = u + 1 → ∀ b : Fin 4,
        ∃ i pci sci, X.get (biasLane L (g / L.block) st.val b, i) =
            some ⟨pci, .arrive (bE L g st) 0 1 true sci⟩ ∧
          arrivals (bE L g st) ((X.tr (biasLane L (g / L.block) st.val b)).take i) = u ∧
          u + 1 ≤ okPolls (bF L g st) ((X.tr (biasLane L (g / L.block) st.val b)).take i) ∧
          WaitObserves X (.thread (biasLane L (g / L.block) st.val b, i)) (tmaLane L X g, j)
            (bE L g st) acq sc := by
  have o := tmaFull hp hX hFw hB g (b_tmaOff st)
  have N := biasFreeHist hp hX hFw g st
  refine ⟨?_, ?_⟩
  · intro b j pc par u acq sc he hu a
    have hlt : u < okPolls (bF L g st) (X.tr (biasLane L (g / L.block) st.val b)) := by
      rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
    obtain ⟨hS, hub⟩ := (biasRing hp hX hFw hB g st).full_observes hX (b := b) hlt a.succ
    obtain ⟨-, -, h1⟩ := o.source hS
    obtain ⟨⟨pci, al, sp, hget, hm⟩, hcnt⟩ := h1 (by simp)
    obtain ⟨i, hi, -, hpol⟩ := tmaFull_pol hp hX hFw hB g (b_tmaOff st) hS
    rw [hi] at hget hcnt
    rw [bE_eq] at hpol
    change MBarrier.UpdateBeforeWait _ (TmaUnits.it X (bF L g st) (tmaLane L X g) 2 a.succ u)
      (Ref.thread (biasLane L (g / L.block) st.val b, Poll.nth X (bF L g st)
        (biasLane L (g / L.block) st.val b) u)) at hub
    rw [show Poll.nth X (bF L g st) (biasLane L (g / L.block) st.val b) u = j by
      rw [← hu]; exact Poll.nth_eq he,
      show TmaUnits.it X (bF L g st) (tmaLane L X g) 2 a.succ u =
        .async (tmaLane L X g, i) (.notify .load) by
      simp only [TmaUnits.it, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte]
      rw [← hi]] at hub
    exact ⟨i, pci, al, sp, hget, hm, by simpa using hcnt, hpol, ⟨⟨pc, par, he⟩, hub⟩⟩
  · intro j pc par u acq sc he hu b
    have hlt : u + 1 < okPolls (bE L g st) (X.tr (tmaLane L X g)) := by
      rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
    obtain ⟨hS, hub⟩ := (biasRing hp hX hFw hB g st).empty_observes hX (a := 0) hlt b
    obtain ⟨-, ⟨pci, sci, hget⟩, hcnt⟩ := N.S_rec hS
    obtain ⟨i, hi, -, hpoll⟩ := (biasRing hp hX hFw hB g st).polE (b, u) hS
    change Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) b u =
      (biasLane L (g / L.block) st.val b, i) at hi
    change MBarrier.UpdateBeforeWait _
      (Ref.thread (Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) b u))
      (Ref.thread (tmaLane L X g, Poll.nth X (bE L g st) (tmaLane L X g) (u + 1))) at hub
    rw [hi] at hub hget hcnt
    rw [show Poll.nth X (bE L g st) (tmaLane L X g) (u + 1) = j by
      rw [← hu]; exact Poll.nth_eq he] at hub
    exact ⟨i, pci, sci, hget, hcnt, hpoll, ⟨⟨pc, par, he⟩, hub⟩⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
