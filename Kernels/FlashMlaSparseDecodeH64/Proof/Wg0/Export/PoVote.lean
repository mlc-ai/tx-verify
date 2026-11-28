-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Lemmas.Tcgen05.TcFence
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Lemmas.Kernel.UbLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # The exchange load is before every later event of its lane

The vote at pc 578 is no memory access, so the exchange load at pc 572 before it is in program
order before the vote, and the vote before every later event of the lane: the exchange load is
below every later event in the order of the tcgen05 proofs (`w0_tc_572`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The vote is no memory access.** -/
theorem w0_vote_noAcc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 578) : e.acc = none := by
  obtain ⟨d, -, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw he hub (by omega)
  have hs : d.site = .vote := Wg0.site_vote_of_pc (hpc'.symm.trans hpc)
  obtain ⟨pc, kd⟩ := e
  simp only [Wg0.EvK, hs] at hk
  rcases hk with ⟨p, r, hk⟩ | ⟨f, hk⟩ <;> simp [Event.acc, hk]

/-- **The exchange load is below every later event of its lane** (a path of `TcStep` edges),
given the valid prefix through the load. -/
theorem w0_tc_572 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {kt k : Nat} {f : Event}
    (hf : X.get (g, kt) = some f) (hpc : f.pc = 572)
    (hv : W0Valid P.scale ((X.tr g).take (kt + 1))) (hk : kt < k) (hkl : k < (X.tr g).length) :
    Relation.TransGen (TcMma.TcStep L X) (g, kt) (g, k) := by
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, kt + 1) = some e' :=
    ⟨_, (List.getElem?_eq_getElem (by omega : kt + 1 < (X.tr g).length) : (X.tr g)[kt + 1]? = _)⟩
  have hacc : (X.get (g, kt + 1)).bind Event.acc = none := by
    rw [he']
    by_cases hub : ∀ u, e'.kind ≠ .ub u
    · exact w0_vote_noAcc hp hX hFw he' hub (Wg0.w0_next_572 hp hX hFw hw hf hpc he' hub hv)
    · obtain ⟨u, hu⟩ := not_forall.mp hub
      obtain ⟨pc, kd⟩ := e'
      obtain rfl : kd = .ub u := not_not.mp hu
      rfl
  have h1 : po X (g, kt) (g, kt + 1) :=
    po_of_not_access (e := (g, kt)) (f := (g, kt + 1)) rfl (by simp) (by simp; omega) hacc
  rcases Nat.eq_or_lt_of_le (show kt + 1 ≤ k by omega) with rfl | hlt
  · exact .single (.inl (.single (.inl h1)))
  · exact .head (.inl (.single (.inl h1)))
      (.single (.inl (.single (.inl (po_of_source_not_access rfl hlt hkl hacc)))))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
