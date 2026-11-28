-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryRoute
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryLanes
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

def query_parameters (Q : Params) := [(param "25",Q.nTok),(param "11",Q.lseBase),
  (param "10",Q.oBase)]

theorem seg_query_params {Q L g w d} :
    Seg kernel Assumptions.all (explicitParams L (query_parameters Q)) g 3 316
      (facts Q L g w d 316) 319 (facts Q L g w d 319) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_plain]
    seg_close [registerValue,query_parameters,MemExt.extendBits_same,u32,b32,b64])

/-- The three parameter loads of the query entry, in the launch itself. -/
theorem seg_query_params_pre {Q L m g w d} (hp : Pre Q L m) :
    Seg kernel Assumptions.all L g 3 316 (facts Q L g w d 316) 319 (facts Q L g w d 319) := by
  have h : explicitParams L (query_parameters Q) = L := by
    apply explicitParams_eq
    intro p v hm
    simp only [query_parameters,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hm
    rcases hm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hp.paramNTok
    · exact hp.paramLse
    · exact hp.paramO
  have params := seg_query_params (Q := Q) (L := L) (g := g) (w := w) (d := d)
  rw [h] at params
  exact params

/-- The control run from the end of the copy tail to the two moves of the loads. -/
theorem query_start_386 {Q L m g w d} (hp : Pre Q L m) :
    SegU kernel Assumptions.all L g 316 (facts Q L g w d 316) 386 (facts Q L g w d 386) := by
  have params := seg_query_params_pre (Q := Q) (L := L) (g := g) (w := w) (d := d) hp
  apply (SegU.of_seg params).comp
  apply SegU.comp (b := 320) (G := facts Q L g w d 320)
  · apply Lib.sum_span (V := valueOf Q L g w d) (rs := ctlLive 319) (rs' := ctlLive 320)
      (r := 463) (dst := 491) (δ := 256) false (by decide) Flow.code_319 (by decide +kernel)
      (by decide +kernel) rfl (fun _ _ => ⟨rfl,rfl⟩)
    intro r hr
    have keys : (ctlLive 320).all (fun r => decide (r=491 ∨ r ∈ ctlLive 319)) := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp keys r hr)
  · exact query_lanes_386

theorem query_start {Q L m g w d} (hp : Pre Q L m) :
    let s := querySite (g%L.block) d 0
    SegU kernel Assumptions.all L g 316 (facts Q L g w d 316) s.pc (facts Q L g w d s.pc) :=
  (query_start_386 hp).comp (query_dflt.comp
    (query_route 0).1)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
