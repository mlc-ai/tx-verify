-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
import Kernels.InklingRelDecode.Proof.Lib.RawArith
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section
variable {L : Launch} {g pc : Nat} {w : Value} {regs : Nat → Value}

/-- The block table is read as a scalar word. A malformed byte array faults on load,
while a rebuilt value lacking an integer pattern faults at the following mad.lo. -/
private theorem recordPage {C : Flow.Code kernel Assumptions.all L g} (d : C.D)
    (dn : Value → C.D) {a : MemAccess} {r : Nat}
    (hc : kernel.code[C.pc d]? = some ⟨none, .mem a⟩) (loc : (Op.mem a).isLocal = false)
    (hk : a.kind = .load) (hnc : a.nc = false) (hext : a.ext = .same) (hr : a.regs = [r])
    (hs : C.sub d = 0) (ha : C.acc d = []) (hfree : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hnext : ∀ x bs, C.next d ⟨C.pc d, .rd x bs⟩ = (rebuild 3 bs).toOption.map
      (fun v => some (dn v)))
    (hsub : ∀ v, C.sub (dn v) = 0) (hacc : ∀ v, C.acc (dn v) = [])
    (hinv : ∀ v, C.inv (dn v))
    (span : ∀ v, SegU kernel Assumptions.all L g (C.pc d + 1) ((r, v) :: C.facts d)
      (C.pc (dn v)) (C.facts (dn v))) : C.StepAtU d where
  site := fun _ => ⟨_, hc, loc, trivial⟩
  step := by
    intro t e u ins hat _ hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
    rw [hr]
    cases hv : rebuild 3 bs with
    | error f =>
      refine .inr ⟨by rw [hnext, hv]; rfl, Machine.dead_of_fault (f := f) ?_⟩
      simp only [afterLoad, hv]
    | ok v =>
      have ht := Code.at_of_atD hat hs ha
      obtain ⟨_, hsub0, hacc0, _, _⟩ := id ht
      rw [afterLoad_ok hsub0 hacc0 hv]
      have heq : {setReg t r v with pc := t.pc + 1, sub := 0, acc := []} =
          PTX.next (setReg t r v) := by cases t; simp_all [PTX.next, setReg]
      rw [heq]
      obtain ⟨u, hrun, hu⟩ := Code.landsU (C := C) (d := dn v)
        (At.set ht hfree) (span v) (hinv v) (hsub v) (hacc v)
      exact .inl (.inr ⟨dn v, u, by rw [hnext, hv]; rfl, hrun, hu⟩)

private theorem freshPair {pc r s : Nat} {v : Value} {val : Nat → Value}
    (hrs : s ≠ r) (hl : r ∉ Flow.live pc) :
    ∀ q ∈ (s, v) :: factsFrom (Flow.live pc) val, q.1 ≠ r := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hrs
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact fun he => hl (he ▸ hj)

variable (i n a b : Value)

private abbrev pageFacts (d : D) := factsFrom (Flow.live d.site.pc) (valueOf L g w regs d)

private theorem madValue (v p : Value) (row : BitVec 64) :
    truncBits 32 (bits v * bits p + bits (.bits 32 row)) =
      Arith32.mad32 (bits v) (bits p) row := by
  simp only [bits, Arith32.mad32, Arith32.r32, Value.regBits, Option.getD_some, truncBits_idem]

private theorem page0_span (v : Value) :
    SegU kernel Assumptions.all L g 2383
      ((581, v) :: pageFacts (L := L) (g := g) (w := w) (regs := regs) ⟨.page false,i,n,a,b⟩)
      2387 (pageFacts (L := L) (g := g) (w := w) (regs := regs) ⟨.warpBar 0,i,n,v,b⟩) := by
  let val := valueOf L g w regs ⟨.page false,i,n,a,b⟩
  let F := (581, v) :: factsFrom (Flow.live 2382) val
  have head := Lib.madStep (L := L) (g := g) (dst := 584) (F := F)
    (G := (584, .bits 32 (truncBits 32 (bits v * bits (val 529) + bits (val 470)))) :: F)
    Flow.code_2383 (by decide)
    List.mem_cons_self (List.mem_cons_of_mem _ (mem_factsFrom (val := val) (by decide)))
    (List.mem_cons_of_mem _ (mem_factsFrom (val := val) (by decide)))
    (fun _ h => ⟨Function.update_self .., holds_update h (freshPair (by decide) (by decide))⟩)
  have hv : Value.bits 32 (truncBits 32 (bits v * bits (val 529) + bits (val 470))) =
      valueOf L g w regs ⟨.warpBar 0,i,n,v,b⟩ 584 :=
    congrArg (Value.bits 32) (madValue v (regs 529) _)
  rw [hv] at head
  apply head.comp
  apply SegU.of_seg (n := 3)
  intro t ht
  dsimp only [F, val, pageFacts] at ht ⊢
  seg_fp ht using rfl

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem page1_span (v : Value) :
    SegU kernel Assumptions.all L g 2400
      ((591, v) :: pageFacts (L := L) (g := g) (w := w) (regs := regs) ⟨.page true,i,n,a,b⟩)
      2401 (pageFacts (L := L) (g := g) (w := w) (regs := regs) ⟨.warpBar 2,i,n,a,v⟩) := by
  let val := valueOf L g w regs ⟨.page true,i,n,a,b⟩
  let F := (591, v) :: factsFrom (Flow.live 2399) val
  have head := Lib.madStep (L := L) (g := g) (dst := 593) (F := F)
    (G := (593, .bits 32 (truncBits 32 (bits v * bits (val 529) + bits (val 470)))) :: F)
    Flow.code_2400 (by decide)
    List.mem_cons_self (List.mem_cons_of_mem _ (mem_factsFrom (val := val) (by decide)))
    (List.mem_cons_of_mem _ (mem_factsFrom (val := val) (by decide)))
    (fun _ h => ⟨Function.update_self .., holds_update h (freshPair (by decide) (by decide))⟩)
  have hv : Value.bits 32 (truncBits 32 (bits v * bits (val 529) + bits (val 470))) =
      valueOf L g w regs ⟨.warpBar 2,i,n,a,v⟩ 593 :=
    congrArg (Value.bits 32) (madValue v (regs 529) _)
  rw [hv] at head
  apply head.comp
  apply SegU.of_seg (n := 0)
  intro t ht
  dsimp only [F, val, pageFacts] at ht ⊢
  seg_fp ht using rfl

theorem page_step (upper : Bool) : (code L g w regs).StepAtU ⟨.page upper,i,n,a,b⟩ := by
  cases upper
  · apply recordPage (C := code L g w regs) ⟨.page false,i,n,a,b⟩ (fun v => ⟨.warpBar 0,i,n,v,b⟩)
      Flow.code_2382 rfl rfl rfl rfl rfl rfl rfl (by fact_free) _ (fun _ => rfl)
      (fun _ => rfl) (fun _ h => by cases h) (page0_span i n a b)
    intro x bs
    change ((rebuild 3 bs).toOption.bind _) = _
    cases rebuild 3 bs <;> rfl
  · apply recordPage (C := code L g w regs) ⟨.page true,i,n,a,b⟩ (fun v => ⟨.warpBar 2,i,n,a,v⟩)
      Flow.code_2399 rfl rfl rfl rfl rfl rfl rfl (by fact_free) _ (fun _ => rfl)
      (fun _ => rfl) (fun _ h => by cases h) (page1_span i n a b)
    intro x bs
    change ((rebuild 3 bs).toOption.bind _) = _
    cases rebuild 3 bs <;> rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
