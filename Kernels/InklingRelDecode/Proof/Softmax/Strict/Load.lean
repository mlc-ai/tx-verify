-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Adv
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Rescale
public import Lemmas.Flow.StepsQFTv
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The strict step of the accumulator load (pc 2260)

The 64 words it returns are the facts of the registers 1547 to 1610 after it, and the value state
keeps them (`Vals.ov`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt PTX.Kernels.InklingRelDecode.Proof.Iface

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- The destinations of the load: the registers `ovRegs`, which the facts do not name. -/
theorem ld_dests {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hc : kernel.code[2260]? = some ⟨none, .tcLd ds ta sh⟩) :
    ds = Data.ovRegs ∧ (∀ r ∈ Control.ctlLive 2260, r ∉ ds) ∧ ∀ k ∈ Data.dKeys .ldO, k ∉ ds := by
  have h := hc.symm.trans Flow.code_tmemLoad_1
  simp only [Option.some.injEq, Instr.mk.injEq, Op.tcLd.injEq, true_and] at h
  obtain ⟨rfl, rfl, rfl, -⟩ := h
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sstep_ldO (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.ldO, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => Code.tcLdFPv (C := Data.code e L g)
    (d := ⟨⟨.ldO, i, v⟩, w⟩) (f := fun vals => ⟨⟨.waitLdO, i, v⟩, {w with ov := vals}⟩)
    Flow.code_tmemLoad_1 (fun _ h => by cases h)
    (by change Assumptions.all.any (·.tcLdWait 2260) = false; decide +kernel)
    (by decide +kernel) ?_ ?_ (fun a vals => rfl) rfl rfl
    (by change afterF lateQt 2260 _ = true; decide +kernel) (fun _ vals hl hdat => ?_) ev
  · intro p hp
    obtain ⟨-, h1, h2⟩ := ld_dests Flow.code_tmemLoad_1
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact h1 r hr
    · change p ∈ Data.dFS L .ldO w at h
      exact h2 _ (Data.dFS_keys L .ldO w ▸ List.mem_map_of_mem h)
  · exact fun _ he hpc a vals hk v hv =>
      he.tc a vals _ (by rw [hpc]; change 2260 ∈ tcLdPcs; decide) hk v hv
  · obtain ⟨hds, -, -⟩ := ld_dests Flow.code_tmemLoad_1
    have hl64 : vals.length = 64 := hl.trans rfl
    refine ⟨rfl, rfl, Control.body_inv hinv rfl rfl, ?_⟩
    refine SegQ.weaken fun _ hR => holds_of_forall fun q hq => holds_mem hR ?_
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      refine List.mem_append_right _ (List.mem_append_left _ (mem_factsFrom ?_))
      exact (by decide +kernel : ∀ r ∈ Control.ctlLive 2261, r ∈ Control.ctlLive 2260) r hr
    · change q ∈ Data.dFS L .waitLdO {w with ov := vals} at h
      rcases List.mem_append.mp (Data.rs0_of_load (L := L) w hl64 q h) with h1 | h1
      · refine List.mem_append_right _ (List.mem_append_right _ ?_)
        simpa [Data.dF, Data.dFS, Data.inRound] using h1
      · exact List.mem_append_left _ (hds ▸ h1)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
