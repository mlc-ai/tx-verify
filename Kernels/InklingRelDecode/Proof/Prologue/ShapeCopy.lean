-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Shape
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Flow.TmaTmpl
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Control

theorem copy_instr (b : Fin 3) (j : Fin 4) :
    ∃ guard dst coords, kernel.code[(Site.ptc b j).pc]? = some ⟨guard,
      .cpTensor false false dst 0 (.reg 1949) coords (613+2*b.val) 0 none .tile⟩ := by
  fin_cases b <;> fin_cases j
  · exact ⟨_,_,_,Flow.code_211⟩
  · exact ⟨_,_,_,Flow.code_217⟩
  · exact ⟨_,_,_,Flow.code_226⟩
  · exact ⟨_,_,_,Flow.code_231⟩
  · exact ⟨_,_,_,Flow.code_253⟩
  · exact ⟨_,_,_,Flow.code_259⟩
  · exact ⟨_,_,_,Flow.code_268⟩
  · exact ⟨_,_,_,Flow.code_273⟩
  · exact ⟨_,_,_,Flow.code_295⟩
  · exact ⟨_,_,_,Flow.code_301⟩
  · exact ⟨_,_,_,Flow.code_310⟩
  · exact ⟨_,_,_,Flow.code_315⟩

/-- Any issue fired at the four preload sites of a slot debits that slot by 8192 bytes. -/
theorem copy_shape {Q L m g w d t e o ins a sp} (hp : Pre Q L m)
    (ht : (code Q L g w).AtD d t) (b : Fin 3) (j : Fin 4) (hs : d.site = .ptc b j)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (he : e.kind = .tensorIssue a sp) : PTX.MbarRow.Issue e (MbarRow.loc L g (Iface.kvReady b))
      8192 := by
  obtain ⟨guard,dst,cs,fetch⟩ := copy_instr b j
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans fetch)
  have keys : ∀ b : Fin 3, ∀ j : Fin 4,
      613+2*b.val ∈ ctlLive (Site.ptc b j).pc ∧ 1949 ∈ ctlLive (Site.ptc b j).pc := by
    decide +kernel
  obtain ⟨reg,bound,al⟩ := object_reg hp ht (readyIndex b) (hs ▸ (keys b j).1)
  obtain ⟨_,_,_,_,regs⟩ := ht
  have key : 1949 ∈ ctlLive d.site.pc := hs ▸ (keys b j).2
  have ptr : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0) :=
    holds_mem regs (mem_factsFrom key)
  obtain ⟨map,bar,desc,bind,_,spec,_⟩ := tensorLoadCopy_ok (fires_cpTensor_copy hf he)
  obtain ⟨decl,obj⟩ := tensorMapAddress_param ptr map
  obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj (obj.symm.trans hp.paramKv))
  refine ⟨_,_,he,?_,?_⟩
  · rw [← ready_addr b]
    exact Except.ok.inj (bar.symm.trans (mbarLoc_b32 reg bound al))
  · rw [spec]
    have h := Option.some.inj (bind.symm.trans hp.mapKvBind)
    exact (congrArg (fun m : (o : Nat) × TensorDescriptor.Descriptor o =>
      TensorTransfer.bytes m.2) h).trans (by
      simp [TensorTransfer.bytes,mapKv,TensorTile.count,TensorTile.rows,TensorTile.rowsOf,
        TensorTile.step,TensorDescriptor.Format.bytes])

end PTX.Kernels.InklingRelDecode.Proof.Prologue
