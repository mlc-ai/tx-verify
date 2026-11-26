-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane

@[expose] public section

/-! # An event at a coordinate load's pc is a coordinate read

An event of a TMA lane at the pc of coordinate quadruple `q`'s load, which is no undefined
behaviour, is a read at a pc of the role (`tma_coordRd`): the four elements of the load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat}

/-- **An event at a coordinate load's pc is a coordinate read.** -/
theorem tma_coordRd (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {f : Event} {q : Nat} (he : X.get (g, i) = some f) (hq : q < 16)
    (hpc : f.pc = coordLoadPc q) (hub : ∀ fl, f.kind ≠ .ub fl) : tmaRd f = true := by
  have hrange : 2250 ≤ coordLoadPc q ∧ coordLoadPc q ≤ 2300 := by
    simp only [coordLoadPc]; split_ifs <;> omega
  obtain ⟨d, -, -, ⟨hpcd, hE⟩, hl, -⟩ :=
    tma_at hp hX hFw he hub ⟨by rw [hpc]; omega, by rw [hpc]; omega⟩
  tma_state d
  have hr : 2165 ≤ f.pc ∧ f.pc ≤ 2330 := by rw [hpc]; omega
  have hrd : ∀ k : Fin 16, ∀ j : Nat, RdAt L g
      (Tma.crdB L ⟨s, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩) (Tma.coordOff k) 4 j f →
      tmaRd f = true := by
    intro k j h
    rcases h with ⟨a', bs', hk, -⟩ | ⟨fl, hf⟩
    · simp [tmaRd, hk, hr]
    · exact absurd hf (hub fl)
  cases s with
  | coord0 k => exact hrd k 0 hE
  | coord1 k => exact hrd k 1 hE
  | coord2 k => exact hrd k 2 hE
  | coord3 k => exact hrd k 3 hE
  | _ =>
    all_goals first
      | exact absurd rfl (hl _)
      | (exfalso; simp only [Tma.Site.pc] at hpcd; unfold coordLoadPc at hpc;
          split_ifs at hpcd hpc <;> omega)

/-- **No event of the TMA code before an event of the lane is undefined behaviour.** -/
theorem tma_prefix_noUb (hX : Consistent L kernel Assumptions.all m X) {k i : Nat} {e f : Event}
    (he : X.get (g, k) = some e) (hi : i < k) (hf : (X.tr g)[i]? = some f)
    (h1 : 2165 ≤ f.pc) (h2 : f.pc ≤ 2330) : ∀ fl, f.kind ≠ .ub fl := by
  intro fl hk
  have hm : f ∈ (X.tr g).take k :=
    List.mem_iff_getElem?.mpr ⟨i, by rw [List.getElem?_take_of_lt hi]; exact hf⟩
  have := List.countP_eq_zero.mp (lane5_take_noUb hX he) f hm
  simp [Tma.cls, Tma.kindOf, Tma.inRole, hk, h1, h2] at this

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
