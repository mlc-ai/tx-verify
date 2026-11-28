-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.CommitBudget
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Mma.Export.EmptyCredit
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # The empty commits before an issue are counted exactly

If every ordinal up to `T` has its empty commit before position `k`, and none has a larger
ordinal, the commits to slot `s` before `k` are those of the `T` first ordinals of the slot. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow MbarRow

theorem empty_count {Q L m X g k T c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (cta : g/L.block=c)
    (below : ∀ j, j<k → ∀ sp, X.get (g,j)=some ⟨2546,.tc (.commit sp)⟩ →
      pollRound 2510 ((X.tr g).take j) ≤ T)
    (exist : ∀ o, 1 ≤ o → o ≤ T → ∃ j < k, ∃ sp,
      X.get (g,j)=some ⟨2546,.tc (.commit sp)⟩ ∧ pollRound 2510 ((X.tr g).take j) = o) :
    ((X.tr g).take k).countP (commitsTo (Ring.empty.obj L c s)) = visits 0 T s := by
  classical
  refine le_antisymm (commits_visits hp hX hf words warp cta below) ?_
  have pick : ∀ u : Nat, u < visits 0 T s → ∃ j < k, ((X.tr g)[j]?).any
      (commitsTo (Ring.empty.obj L c s)) = true ∧ pollRound 2510 ((X.tr g).take j) = 3*u+s+1 := by
    intro u hu
    have := s.isLt
    unfold visits at hu
    obtain ⟨j,jk,sp,get,ord⟩ := exist (3*u+s+1) (by omega) (by omega)
    refine ⟨j,jk,?_,ord⟩
    obtain ⟨off,rfl,kinds⟩ := Mma.Export.commit hp hX hf warp get
    obtain ⟨-,addr⟩ : 2546 = 2546 ∧ off = Iface.kvEmpty ⟨(pollRound 2510 ((X.tr g).take j) - 1) % 3,
      by omega⟩ := by
      rcases kinds with ⟨h,-⟩|h|⟨h,-⟩|⟨h,-⟩
      · cases h
      · exact h
      · cases h
      · cases h
    subst cta
    rw [show (X.tr g)[j]? = _ from get]
    simp only [Option.any_some, commitsTo, Ring.obj, Ring.offset, decide_eq_true_eq]
    rw [addr]
    congr 3
    ext
    simp only
    omega
  choose! J hJ using pick
  let uses := (Finset.range k).filter fun j => ((X.tr g)[j]?).any (commitsTo (Ring.empty.obj L c s))
  have card : (Finset.range (visits 0 T s)).card ≤ uses.card := by
    apply Finset.card_le_card_of_injOn J
    · intro u hu
      obtain ⟨lt,kind,-⟩ := hJ u (Finset.mem_range.mp hu)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr lt,kind⟩
    · intro u hu v hv same
      obtain ⟨-,-,o1⟩ := hJ u (Finset.mem_range.mp hu)
      obtain ⟨-,-,o2⟩ := hJ v (Finset.mem_range.mp hv)
      have := o1.symm.trans (same ▸ o2)
      omega
  rw [MbarRing.Slot.countP_take_card]
  simpa using card

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
