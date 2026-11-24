-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Lib.NoTc
import Kernels.TmlFa4Fwd.Proof.Mma.Export.ResSched
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word

@[expose] public section

/-! # The warp-collective `tcgen05` instructions of the MMA, output and loader warps

The MMA warp's are its three resource operations (`tc_sched`); the output and loader warps have none
(`noTc_of_warp`). So their lanes agree on them (`tc_uniform`, `tc_unexited`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The lanes of a warp from 12 on agree on their collective `tcgen05` events.** -/
theorem tc_uniform {e f : EvId} {k pc pc' : Nat} {ke kf : TcKind} (hw : SameWarp L e.1 f.1)
    (h12 : 12 ≤ Prologue.warpIndex L e.1) (hke : X.TcK e k) (hkf : X.TcK f k)
    (he : X.get e = some ⟨pc, .tc ke⟩) (hf : X.get f = some ⟨pc', .tc kf⟩) :
    pc = pc' ∧ tcStatic ke = tcStatic kf := by
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨⟨ev, he', hme⟩, hc⟩ := hke
  obtain ⟨⟨fv, hf', hmf⟩, hc'⟩ := hkf
  obtain rfl := Option.some.inj (he.symm.trans he')
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  rcases Nat.lt_or_ge 12 (Prologue.warpIndex L g) with h13 | h13
  · rw [noTc_of_warp hp hX hFw h13 he] at hme
    cases hme
  have hg : Prologue.warpIndex L g = 12 := le_antisymm h13 h12
  have hh : Prologue.warpIndex L h = 12 := hw.2.symm.trans hg
  have e1 := (tc_sched hp hX hFw hg he hme).2
  have e2 := (tc_sched hp hX hFw hh hf hmf).2
  simp only at hc hc'
  rw [hc] at e1
  rw [hc'] at e2
  have hcta : g / L.block = h / L.block := hw.1.2.2
  have hs : resSched L g k = resSched L h k := by
    rcases k with _ | _ | k <;> simp only [resSched, hcta]
  rw [hs, ← e2] at e1
  simp only [Prod.mk.injEq] at e1
  exact ⟨e1.1, by rw [e1.2]⟩

/-- **A lane of a warp from 12 on exits after its warp's collective `tcgen05` events.** -/
theorem tc_unexited {e f : EvId} {k : Nat} (hw : SameWarp L e.1 f.1)
    (h12 : 12 ≤ Prologue.warpIndex L e.1) (hke : X.TcK e k) : ¬ X.ExitedShort isTcColl f k := by
  rintro ⟨⟨pcx, hx⟩, hle⟩
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨⟨ev, he, hme⟩, hc⟩ := hke
  rcases Nat.lt_or_ge 12 (Prologue.warpIndex L g) with h13 | h13
  · rw [noTc_of_warp hp hX hFw h13 he] at hme
    cases hme
  have hg : Prologue.warpIndex L g = 12 := le_antisymm h13 h12
  have hh : Prologue.warpIndex L h = 12 := hw.2.symm.trans hg
  obtain ⟨pc, kd⟩ := ev
  obtain ⟨tk, rfl⟩ := isTcColl_kind hme
  have h3 := (tc_sched hp hX hFw hg he hme).1
  simp only at hc
  have hh3 := (tmem1Facts hp hX hFw).exit hw.1.2.1 hh hx
  have hcnt := mma_tcCount hp hX hFw hh j
  have hsub : ((X.tr h).take j).countP isTcColl ≤ (X.tr h).countP isTcColl :=
    (List.take_sublist _ _).countP_le
  simp only at hle hh3
  omega

end

end PTX.Kernels.TmlFa4Fwd.Proof
