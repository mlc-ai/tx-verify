-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Gate
import Kernels.InklingRelDecode.Proof.Lib.PollBranch
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.BranchU
import Lemmas.Flow.WaitU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof
set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Value}
local notation "tab" => facts e L g v
private def afterReady (e : Entry) (t : Nat) :=
  if e.skip then firstStore e.valid (lead t) else Site.shfl
local notation "z" => afterReady e (g%L.block)

private theorem after_wait : SegU kernel Assumptions.all L g 2567 (tab 2565)
    (z).pc (tab (z).pc) := by
  apply (Lib.control_span (by decide +kernel : Lib.spanCheck ctlLive 2565 2567 2600)).comp
  intro t ht
  obtain ⟨pc,sub,acc,flt,regs⟩ := ht
  have hp := holds_mem regs (mem_factsFrom (by decide : 173 ∈ ctlLive 2600))
  have h := SegU.branch (K := kernel) (L := L) (g := g) (F := tab 2600) e.skip
    Flow.code_2600 Lib.bra_rule (segFree (by decide))
  have start : At t 2600 ((173,.pred e.skip)::tab 2600) := ⟨pc,sub,acc,flt,hp,regs⟩
  refine h.comp ?_ t start
  unfold afterReady
  cases e.skip
  · simp only [Bool.false_eq_true,↓reduceIte]
    exact Lib.control_span (by decide +kernel : Lib.spanCheck ctlLive 2600 2601 2603)
  · simp only [↓reduceIte]
    exact (Lib.control_span (by decide +kernel : Lib.spanCheck ctlLive 2600 2674 2674)).comp
      store_gate

theorem step_wait : (code e L g).StepAtU ⟨.wait,v⟩ := by
  let dst (ok : Bool) : D := ⟨if ok then z else .wait,v⟩
  apply Code.waitU (C := code e L g) (d := ⟨.wait,v⟩) (dst := dst) Flow.code_2565
  · change 2612 ∉ (factsFrom (ctlLive 2565) _).map Prod.fst
    rw [factsFrom_keys]; decide +kernel
  · intro m q ok sc; cases ok <;> rfl
  · rfl
  · rfl
  · intro _; rfl
  · intro _; rfl
  · rintro (_|_)
    · trivial
    · change Inv e _ ⟨z,v⟩
      unfold afterReady
      split
      · exact first_inv ..
      · trivial
  · rintro (_|_)
    · exact Lib.poll_branch (pc := 2566) false Flow.code_2566 (by decide)
    · exact (Lib.poll_branch (pc := 2566) true Flow.code_2566 (by decide)).comp after_wait

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
