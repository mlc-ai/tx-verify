-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Advance
import Kernels.InklingRelDecode.Flow.Code.Part002
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Kernels.InklingRelDecode.Flow.Code.Part008
import Lemmas.Flow.IssueNext
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

def pbTail (b : Fin 3) (j : Fin 4) : Site :=
  match j with
  | 0 => .psh b
  | 1 => .pel b 1
  | 2 => .pel b 2
  | 3 => .pel b 3

def pbBar (b : Fin 3) (j : Fin 4) : Site := .pb b ⟨j.val+1,by omega⟩

theorem pbt_fetch (b : Fin 3) (j : Fin 4) : kernel.code[(pbBar b j).pc]? =
    some ⟨none,.barSyncN (.imm 0) (.imm 128) true⟩ := by
  fin_cases b <;> fin_cases j
  · exact Flow.code_201
  · exact Flow.code_212
  · exact Flow.code_222
  · exact Flow.code_227
  · exact Flow.code_243
  · exact Flow.code_254
  · exact Flow.code_264
  · exact Flow.code_269
  · exact Flow.code_285
  · exact Flow.code_296
  · exact Flow.code_306
  · exact Flow.code_311

theorem pbt_frames : ∀ b j,
    (pbBar b j).pc+1 = (pbTail b j).pc ∧
    (ctlLive (pbTail b j).pc).isSublist (ctlLive (pbBar b j).pc) := by decide +kernel

/-- The last four counted barriers of each preload go directly to a warp collective. -/
theorem step_preload_bar {Q L g w} (d : D) (b : Fin 3) (j : Fin 4)
    (hs : d.site = .pb b ⟨j.val+1,by omega⟩) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨pbBar b j,a,x,c,won,bcast⟩
  obtain ⟨pc,live⟩ := pbt_frames b j
  apply straight (d := d) (z := pbTail b j) (pbt_fetch b j) rfl (fun _ => trivial)
    fires_barSyncN_next _ rfl _ _ (samePc pc live)
  · intro e; fin_cases j <;> rfl
  · fin_cases j <;> rfl
  · fin_cases j <;> trivial

/-- Both shared proxy fences go directly to their next event. -/
theorem step_fence {Q L g w} (d : D) (hs : d.site = .fnc0 ∨ d.site = .fnc1) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  rcases hs with h|h <;> cases h
  · exact straight Flow.code_179 rfl (fun _ => trivial) (fun h => fires_next (by trivial) h)
      (fun _ => rfl) rfl rfl trivial (samePc rfl (by
        change (ctlLive 180).isSublist (ctlLive 179) = true; decide))
  · exact straight Flow.code_569 rfl (fun _ => trivial) (fun h => fires_next (by trivial) h)
      (fun _ => rfl) rfl rfl trivial (samePc rfl (by
        change (ctlLive 570).isSublist (ctlLive 569) = true; decide))

theorem step_join {Q L g w} (d : D) (hs : d.site = .bar18) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  apply straight (d := ⟨.bar18,a,x,c,won,bcast⟩) (z := .exit) Flow.code_573 rfl
    (fun _ => trivial) _ (fun _ => rfl)
    rfl rfl trivial (samePc rfl (by
        change (ctlLive 574).isSublist (ctlLive 573) = true; decide))
  intro t ev u hf
  change ev = _ ∧ some u = some (PTX.next t) at hf
  exact Option.some.inj hf.2

theorem step_handoff {Q L g w} (d : D) (hs : d.site = .exit) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  exact ⟨fun _ => ⟨_,Flow.code_574,rfl,trivial⟩,fun _ _ _ _ _ => .inl (.inl rfl)⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
