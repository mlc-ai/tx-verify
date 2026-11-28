-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Address
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof

def storeCheck (pc pred : Nat) := match kernel.code[pc]? with
  | some ⟨some (p,neg),.mem a⟩ =>
    p==pred && !neg && a.kind==MemKind.store && a.srcs.length==1 && !(Op.mem a).isLocal
  | _ => false

theorem store_fetch {p r} (h : storeCheck p r=true) :
    ∃ a : MemAccess, kernel.code[p]?=some ⟨some (r,false),.mem a⟩ ∧ a.kind=.store ∧
      a.srcs.length=1 ∧
      (Op.mem a).isLocal=false := by
  unfold storeCheck at h; split at h
  · rename_i q neg a hc
    simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨rfl,rfl⟩,kind⟩,len⟩,nl⟩ := h
    exact ⟨a,hc,kind,len,nl⟩
  · cases h

theorem guarded_store {e L g v r} {s z : Site} (fetch : storeCheck s.pc r)
    (key : r ∈ ctlLive s.pc)
    (guardAt : Inv e (g%L.block) ⟨s,v⟩ → valueOf e L g v r = .pred true)
    (go : ∀ ev, next e L g ⟨s,v⟩ ev = some (some ⟨z,v⟩))
    (ok : Inv e (g%L.block) ⟨s,v⟩ → Inv e (g%L.block) ⟨z,v⟩)
    (span : SegU kernel Assumptions.all L g (s.pc+1) (facts e L g v s.pc) z.pc
      (facts e L g v z.pc)) : (code e L g).StepAtU ⟨s,v⟩ := by
  obtain ⟨a,fetch,kind,len,nl⟩ := store_fetch fetch
  apply straight fetch nl (fun hi => Code.guardTrue_factsFrom key (guardAt hi)) _ go ok span
  intro t ev u sub fire
  obtain ⟨_,_,_,rfl⟩ := fires_st kind fire
  rw [afterStore_last (by omega)]
  cases t; simp_all [PTX.next]

theorem store_checks : ∀ j : Fin 64,
    storeCheck (storePc j) 175 ∧ 175 ∈ ctlLive (storePc j) ∧
      Lib.spanCheck ctlLive (storePc j) (storePc j+1) (storeAt (j.val+1)).pc := by decide +kernel

theorem step_store {e L g v} (j : Fin 64) : (code e L g).StepAtU ⟨.store j,v⟩ := by
  obtain ⟨fetch,key,run⟩ := store_checks j
  apply guarded_store (s := .store j) (z := storeAt (j.val+1)) fetch key _ (fun _ => rfl)
    (fun h => store_inv v h _) (Lib.control_span run)
  exact fun hi => congrArg Value.pred hi

theorem step_lse {e L g v} : (code e L g).StepAtU ⟨.lse,v⟩ := by
  apply guarded_store (s := .lse) (z := .store 0) (r := 174) (by decide +kernel)
    (by decide) _ (fun _ => rfl) (fun h => h.1) addr_from_lse
  intro h
  change Value.pred (lead _ && e.valid) = _
  rw [h.1,h.2]; rfl

/-- A masked output row skips all remaining word stores, including their local unpack steps. -/
theorem skip_stores {e L g v} (off : e.valid=false) {n : Nat} (bound : n≤64) :
    SegU kernel Assumptions.all L g (storeAt n).pc (facts e L g v (storeAt n).pc)
      (storeAt 64).pc (facts e L g v (storeAt 64).pc) := by
  induction bound using Nat.decreasingInduction with
  | self => exact fun t ht => .inl ⟨t,.refl,ht⟩
  | of_succ k hk ih =>
    let j : Fin 64 := ⟨k,hk⟩
    obtain ⟨fetch,key,run⟩ := store_checks j
    obtain ⟨a,ins,_,_,_⟩ := store_fetch fetch
    have val : valueOf e L g v 175 = .pred false := congrArg Value.pred off
    have skip := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g) ins
      (mem_factsFrom_eq key val) rfl
    apply (SegU.of_seg (by simpa only [storeAt,dite_eq_left hk,Site.pc,j,facts] using skip)).comp
    exact (Lib.control_span run).comp ih

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
