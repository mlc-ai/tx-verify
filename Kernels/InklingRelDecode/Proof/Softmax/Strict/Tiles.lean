-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Base
import Kernels.InklingRelDecode.Gen.TypedLateLane02
import Kernels.InklingRelDecode.Gen.TypedLate02
import Lemmas.Flow.StepsQFT
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The strict steps of the score tile -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.Iface PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
open PTX.Kernels.InklingRelDecode.Gen.TypedLate02

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

theorem off_ldS {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hc : kernel.code[1265]? = some ⟨none, .tcLd ds ta sh⟩) :
    (∀ r ∈ Control.ctlLive 1265, r ∉ ds) ∧ 498 ∉ ds ∧ 1914 ∉ ds := by
  have h := hc.symm.trans Flow.code_tmemLoad_0
  simp only [Option.some.injEq, Instr.mk.injEq, Op.tcLd.injEq, true_and] at h
  obtain ⟨rfl, rfl, rfl, -⟩ := h
  decide +kernel

theorem sstep_ldS (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.ldS, i, v⟩, w⟩ ev := by
  refine Code.tcLdFP (C := Data.code e L g) (d := ⟨⟨.ldS, i, v⟩, w⟩)
    (f := fun vals => ⟨⟨.waitLd, i, v⟩, {w with s := vals}⟩)
    Flow.code_tmemLoad_0 (fun _ h => by cases h)
    (by change Assumptions.all.any (·.tcLdWait 1265) = false; decide +kernel)
    (by decide +kernel) ?_ (fun ev hw hpc a vals hk => ?_) (fun a vals => rfl) rfl rfl
    (by change afterF lateQt 1265 _ = true; decide +kernel) (fun hinv vals hlen hdat => ?_) ev
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := off_ldS Flow.code_tmemLoad_0
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact h1 r hr
    · simp [Data.dF, Data.dFS, Data.inRound] at h
      rcases h with h | h
      · rw [h]; exact h2
      · rw [h]; exact h3
  · exact hw.tc a vals _ (by rw [hpc]; change 1265 ∈ tcLdPcs; decide) hk
  · refine ⟨rfl, rfl, Control.body_inv hinv rfl rfl, ?_⟩
    have hG : ∀ p ∈ (Data.code e L g).facts ⟨⟨.waitLd, i, v⟩, {w with s := vals}⟩,
        p ∈ (Data.code e L g).facts ⟨⟨.ldS, i, v⟩, w⟩ := by
      intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact List.mem_append_left _ (Control.project (p := 1265) (q := 1298)
          (by decide +kernel) p h)
      · exact List.mem_append_right _ (by simpa [Data.dF, Data.dFS, Data.inRound] using h)
    have hW : ∀ p ∈ (Data.code e L g).facts ⟨⟨.waitLd, i, v⟩, {w with s := vals}⟩,
        p.1 ∉ l02_1266_wr := by
      intro p hp
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact (by decide +kernel : ∀ r ∈ Control.ctlLive 1298, r ∉ l02_1266_wr) r hr
      · simp [Data.dF, Data.dFS, Data.inRound] at h
        have k : 498 ∉ l02_1266_wr ∧ 1914 ∉ l02_1266_wr := by decide +kernel
        rcases h with h | h <;> rw [h]
        exacts [k.1, k.2]
    exact lw_l02_1266 (A := Assumptions.all) (R := LateR' L g) (fp3_of (by decide +kernel)) hW hG
      (fun _ h => nomatch h) (fun _ h => nomatch h)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
