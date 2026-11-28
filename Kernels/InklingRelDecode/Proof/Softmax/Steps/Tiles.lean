-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Lemmas.Flow.Step.GuardedLoadU
import Kernels.InklingRelDecode.Flow.Code
import Kernels.InklingRelDecode.Proof.Softmax.FloatPlain

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

theorem step_ldS : (code e L g).StepAtU ⟨.ldS,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.tcLoadU (C := code e L g) (d := ⟨.ldS,i,v⟩) (dn := ⟨.waitLd,i,v⟩)
    (live := ctlLive 1265) Flow.code_tmemLoad_0 (fun _ h => by cases h)
    (by change Assumptions.all.any (·.tcLdWait 1265) = false; decide +kernel)
    rfl (by decide +kernel) (fun _ _ => rfl) rfl rfl rfl rfl (body_inv hi rfl rfl)
  apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by decide : 1266 ≤ 1298)
    (by decide +kernel : 1298 ≤ kernel.code.length)
  · change Havoc.check Lib.hooks ((facts e L g ⟨.waitLd,i,v⟩ 1298).map Prod.fst) 1266 1298 _ = true
    rw [facts,factsFrom_keys]
    decide +kernel
  · exact project (p := 1265) (q := 1298) (by decide +kernel)

theorem step_ldO : (code e L g).StepAtU ⟨.ldO,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.tcLoadU (C := code e L g) (d := ⟨.ldO,i,v⟩) (dn := ⟨.waitLdO,i,v⟩)
    (live := ctlLive 2260) Flow.code_tmemLoad_1 (fun _ h => by cases h)
    (by change Assumptions.all.any (·.tcLdWait 2260) = false; decide +kernel)
    rfl (by decide +kernel) (fun _ _ => rfl) rfl rfl rfl rfl (body_inv hi rfl rfl)
  exact project_seg (p := 2260) (q := 2261) (by decide +kernel)

theorem step_store10 : (code e L g).StepAtU ⟨.store10,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.vstU (C := code e L g) (d := ⟨.store10,i,v⟩) (dn := ⟨.bar23,i,v⟩)
    Flow.code_store_10 rfl rfl (fun _ => rfl) rfl
  · exact fun h => (Nat.lt_irrefl 1 h).elim
  · intro _
    exact ⟨rfl,rfl,body_inv hi rfl rfl,project_seg (p := 2250) (q := 2251) (by decide +kernel)⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
