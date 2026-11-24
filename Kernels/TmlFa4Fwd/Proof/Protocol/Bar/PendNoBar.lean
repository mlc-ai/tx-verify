-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemStore
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemLoad
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemStore
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unnecessarySeqFocus false

@[expose] public section

/-! # The states between an access and its wait fire no barrier-2 event

The correction stage loop (`StPend`), the softmax P stores and store waits (`PstPend`) and the
softmax load regions (`LdPend`) fire loads, stores, waits, reads, fences, mbarrier operations and
the named barriers 11, 12 and `nbW` (3 to 10), never barrier 2 (`stp_nobar`, `pstp_nobar`,
`ldp_nobar`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem stp_nobar {st : Fin 2} {d : Correction.D} {pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (hp : StPend st d.site = true) (hev : Correction.Ev p L g d ⟨pc, .bar 2 cnt mode⟩) : False := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [StPend, Bool.false_eq_true] at hp <;> simp only [Correction.Ev] at hev <;>
    simp_all

theorem pstp_nobar {r : Softmax.Rd} {d : Softmax.D} {pc : Nat} {cnt : Option Nat}
    {mode : BarMode} (hp : PstPend r d.site = true)
    (hev : Softmax.Ev p L g d ⟨pc, .bar 2 cnt mode⟩) : False := by
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [PstPend, Bool.false_eq_true] at hp <;> simp only
      [Softmax.Control.D.scheduler, Softmax.Ev] at hev <;>
    (try split at hev) <;> simp_all

theorem ldp_nobar (hp8 : g % L.block / 32 < 8) {r : Softmax.Rd} {d : Softmax.Control.D} {pc : Nat}
    {cnt : Option Nat} {mode : BarMode} (hp : LdPend r d)
    (hev : Softmax.Ev p L g d ⟨pc, .bar 2 cnt mode⟩) : False := by
  have h3 := soft_nb_range (L := L) (g := g) hp8
  obtain ⟨s, v, k, acc⟩ := d
  rcases hp with hm | ⟨hs, hk, -⟩ | ⟨c, hs, hk, -⟩
  · cases r <;> simp only [ldSites, List.mem_append, List.mem_map, List.mem_finRange, true_and,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    · rcases hm with (((⟨c, rfl⟩ | rfl) | ⟨c, rfl⟩) | rfl | rfl | rfl | rfl) <;>
        simp only [Softmax.Control.D.scheduler, Softmax.Ev] at hev <;> (try split at hev) <;>
        (try simp_all [Softmax.tcLdOrUb, Softmax.rdOrUb]) <;>
        (try (split at hev <;> simp_all)) <;> (try omega)
    · rcases hm with (((⟨c, rfl⟩ | rfl) | ⟨c, rfl⟩) | rfl | rfl | rfl | rfl | rfl) <;>
        simp only [Softmax.Control.D.scheduler, Softmax.Ev] at hev <;> (try split at hev) <;>
        (try simp_all [Softmax.tcLdOrUb, Softmax.rdOrUb]) <;>
        (try (split at hev <;> simp_all)) <;> (try omega)
  · simp only at hs; subst hs
    simp only [Softmax.Control.D.scheduler, Softmax.Ev] at hev
    split_ifs at hev <;> simp_all [Softmax.tcLdOrUb]
  · simp only at hs; subst hs
    simp only [Softmax.Control.D.scheduler, Softmax.Ev] at hev
    split_ifs at hev <;> simp_all [Softmax.tcLdOrUb]

end
end PTX.Kernels.TmlFa4Fwd.Proof
