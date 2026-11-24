-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedTail
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
import Lemmas.Flow.PackMul
import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

def repeatedScoreWordBase (mode : Repeated) (quarter : Fin 4) : Nat :=
  (if mode = .biased then 4038 else 5188)+32*quarter.val

/-- The decoded low-to-high QK pair for a repeated score load. -/
def repeatedScorePairReg (mode : Repeated) (quarter : Fin 4) (pair : Nat) : Nat :=
  match mode with
  | .biased => 7367+16*quarter.val+pair
  | .unbiased =>
    if quarter = 0 ∧ pair < 4 then 8690-pair else 7427+16*quarter.val+pair

def repeatedScoreWordRegs (mode : Repeated) (quarter : Fin 4) :=
  (List.range 32).map (repeatedScoreWordBase mode quarter + ·)

private theorem repeatedScoreDecode (mode : Repeated) (quarter : Fin 4) :
    kernel.code[scorePc mode.round quarter]? = some
      ⟨none,.tcLd (repeatedScoreWordRegs mode quarter)
        (scoreReg mode.round quarter) .s32x32b none⟩ := by
  cases mode <;> fin_cases quarter
  · exact Flow.code_5112
  · exact Flow.code_5129
  · exact Flow.code_5146
  · exact Flow.code_5163
  · exact Flow.code_6679
  · exact Flow.code_6696
  · exact Flow.code_6713
  · exact Flow.code_6730

private def repeatedScorePacks (mode : Repeated) (quarter : Fin 4) :
    List (Nat × Nat × Nat) :=
  (List.range 16).map fun k =>
    let pair := 15-k
    let base := repeatedScoreWordBase mode quarter
    (repeatedScorePairReg mode quarter pair,base+2*pair,base+2*pair+1)

private theorem biasedPackCode0 :
    packCodeB kernel (scorePc (Repeated.round .biased) 0+1)
      (repeatedScorePacks .biased 0) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem biasedPackCode1 :
    packCodeB kernel (scorePc (Repeated.round .biased) 1+1)
      (repeatedScorePacks .biased 1) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem biasedPackCode2 :
    packCodeB kernel (scorePc (Repeated.round .biased) 2+1)
      (repeatedScorePacks .biased 2) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem biasedPackCode3 :
    packCodeB kernel (scorePc (Repeated.round .biased) 3+1)
      (repeatedScorePacks .biased 3) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem unbiasedPackCode0 :
    packCodeB kernel (scorePc (Repeated.round .unbiased) 0+1)
      (repeatedScorePacks .unbiased 0) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem unbiasedPackCode1 :
    packCodeB kernel (scorePc (Repeated.round .unbiased) 1+1)
      (repeatedScorePacks .unbiased 1) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem unbiasedPackCode2 :
    packCodeB kernel (scorePc (Repeated.round .unbiased) 2+1)
      (repeatedScorePacks .unbiased 2) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem unbiasedPackCode3 :
    packCodeB kernel (scorePc (Repeated.round .unbiased) 3+1)
      (repeatedScorePacks .unbiased 3) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem repeatedPackCode (mode : Repeated) (quarter : Fin 4) :
    PackCode kernel (scorePc mode.round quarter+1) (repeatedScorePacks mode quarter) := by
  apply PackCode.of_bool
  cases mode <;> fin_cases quarter
  · exact biasedPackCode0
  · exact biasedPackCode1
  · exact biasedPackCode2
  · exact biasedPackCode3
  · exact unbiasedPackCode0
  · exact unbiasedPackCode1
  · exact unbiasedPackCode2
  · exact unbiasedPackCode3

private theorem repeatedPackCore : NoPack Assumptions.all := by
  intro d a b l g t ax h
  simp only [Assumptions.all,Assumptions.numeric,Assumptions.synchronization,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem repeatedPackSegFree (mode : Repeated) (q : Fin 4) {i : Nat} (hi : i < 16) :
    SegFreePc Assumptions.all (scorePc mode.round q+1+i) := by
  have hSegment : scorePc mode.round q+1+i ∉ Assumptions.swExp2Sites := by
    cases mode <;> fin_cases q <;> interval_cases i <;> decide
  intro ax ha l g t ht
  rw [Assumptions.all,List.mem_append,List.mem_append,List.mem_singleton] at ha
  rcases ha with (ha | ha) | rfl
  · exact Assumptions.numeric_segSites ax ha l g t (ht.symm ▸ hSegment)
  · simp only [Assumptions.synchronization,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- Decode the 16 local packs after a returning repeated score load. -/
theorem repeatedScorePackLocal {l : Launch} {g : Nat}
    (mode : Repeated) (quarter : Fin 4) {t : TState} {F : List (Nat × Value)}
    (ht : At t (scorePc mode.round quarter) F)
    (vals : List Value) (hLength : vals.length = 32)
    (hBytes : ∀ k < 32, (vals.getD k (b32 0)).bytes = 4) :
    let loaded := setRegs (next t) (repeatedScoreWordRegs mode quarter) vals
    ∃ u, At u (scorePc mode.round quarter+17) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) loaded u ∧
      (∀ k < 16, u.regs (repeatedScorePairReg mode quarter k) =
        some (joinValue (vals.getD (2*k) (b32 0)) (vals.getD (2*k+1) (b32 0)))) ∧
      (∀ r, (r < repeatedScoreWordBase mode quarter ∨ repeatedScoreWordBase mode quarter+32 ≤ r) →
        (∀ k < 16, r ≠ repeatedScorePairReg mode quarter k) → u.regs r = t.regs r) := by
  let raw := repeatedScoreWordBase mode quarter
  let pair := repeatedScorePairReg mode quarter
  let ds := repeatedScoreWordRegs mode quarter
  let loaded := setRegs (next t) ds vals
  let words := fun r => vals.getD (r-raw) (b32 0)
  let packs := repeatedScorePacks mode quarter
  have hNodupWords : ds.Nodup := by cases mode <;> fin_cases quarter <;> decide
  have hReg (n : Nat) (hn : n < 32) :
      loaded.regs (raw+n) = some (vals.getD n (b32 0)) := by
    apply setRegs_get _ _ _ n _ _ hNodupWords
    · simp only [ds,repeatedScoreWordRegs,raw,List.getElem?_map,List.getElem?_range hn,
        Option.map_some]
    · have hIndex : n < vals.length := by omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hIndex,Option.getD_some]
  have hLoaded : At loaded (scorePc mode.round quarter+1) [] := by
    have hS := setRegs_skel (next t) ds vals
    exact ⟨hS.1.trans (congrArg (·+1) ht.1),hS.2.1.trans ht.2.1,
      hS.2.2.1.trans ht.2.2.1,hS.2.2.2.trans ht.2.2.2.1,trivial⟩
  have hP {p : Nat × Nat × Nat} (hm : p ∈ packs) :
      ∃ k < 16, p = (pair k,raw+2*k,raw+2*k+1) := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    have h := List.mem_range.mp hi
    exact ⟨15-i,by omega,rfl⟩
  have hSource (p : Nat × Nat × Nat) (hm : p ∈ packs) :
      loaded.regs p.2.1 = some (words p.2.1) ∧ loaded.regs p.2.2 = some (words p.2.2) := by
    obtain ⟨k,hk,rfl⟩ := hP hm
    change loaded.regs (raw+2*k) = some (words (raw+2*k)) ∧
      loaded.regs (raw+2*k+1) = some (words (raw+2*k+1))
    simp only [words,Nat.add_sub_cancel_left, Nat.add_assoc]
    exact ⟨hReg _ (by omega),hReg _ (by omega)⟩
  have hGap (k : Nat) (hk : k < 16) : raw+32 ≤ pair k := by
    have hQ := quarter.isLt
    cases mode
    · simp [raw,pair,repeatedScoreWordBase,repeatedScorePairReg]
      omega
    · by_cases hCase : quarter = 0 ∧ k < 4 <;>
        simp [raw,pair,repeatedScoreWordBase,repeatedScorePairReg,hCase] <;> omega
  have hDis (p : Nat × Nat × Nat) (hp : p ∈ packs) (q : Nat × Nat × Nat) (hq : q ∈ packs) :
      q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2 := by
    obtain ⟨i,hi,rfl⟩ := hP hp
    obtain ⟨j,hj,rfl⟩ := hP hq
    have h := hGap j hj
    change pair j ≠ raw+2*i ∧ pair j ≠ raw+2*i+1
    omega
  have hForm : packsOk words packs = true := by
    apply List.all_eq_true.mpr
    intro p hm
    obtain ⟨k,hk,rfl⟩ := hP hm
    have hB := hBytes
    have hLo : (words (raw+2*k)).bytes = 4 := by
      rw [show words (raw+2*k) = vals.getD (2*k) (b32 0) by simp [words]]
      exact hB (2*k) (by omega)
    have hHi : (words (raw+2*k+1)).bytes = 4 := by
      rw [show words (raw+2*k+1) = vals.getD (2*k+1) (b32 0) by simp [words,Nat.add_assoc]]
      exact hB (2*k+1) (by omega)
    change ((words (raw+2*k)).bytes == 4 && (words (raw+2*k+1)).bytes == 4) = true
    simp [hLo,hHi]
  have hLocal := (packs_run (K := kernel) (L := l) (g := g) repeatedPackCore words packs loaded
    (hLoaded.1.symm ▸ repeatedPackCode mode quarter) hLoaded.2.2.2.1 hSource hDis
    (fun i hi => hLoaded.1.symm ▸ repeatedPackSegFree mode quarter hi)).1 hForm
  let u := packRun words loaded packs
  have hLast := packRun_skel words packs loaded
  have hAt : At u (scorePc mode.round quarter+17) [] := by
    have hLen : packs.length = 16 := by simp [packs,repeatedScorePacks]
    exact ⟨by rw [hLast.1,hLoaded.1,hLen],hLast.2.1.trans hLoaded.2.1,
      hLast.2.2.1.trans hLoaded.2.2.1,hLast.2.2.2.trans hLoaded.2.2.2.1,trivial⟩
  refine ⟨u,hAt,run_rtg hLocal,?_,?_⟩
  · intro k hk
    have hNodup : (packs.map Prod.fst).Nodup := by cases mode <;> fin_cases quarter <;> decide
    have hm : (pair k,raw+2*k,raw+2*k+1) ∈ packs := by
      apply List.mem_map.mpr
      refine ⟨15-k,List.mem_range.mpr (by omega),?_⟩
      dsimp only
      rw [show 15-(15-k) = k by omega]
    have h := packRun_val words packs loaded hNodup hm
    simpa only [words,Nat.add_assoc,Nat.add_sub_cancel_left] using h
  · intro r hr hpr
    have hPack := packRun_other words (r := r) packs loaded (by
      intro p hm
      obtain ⟨k,hk,rfl⟩ := hP hm
      exact (hpr k hk).symm)
    have hRaw : r ∉ ds := by
      intro hm
      obtain ⟨k,hk,e⟩ := List.mem_map.mp hm
      have hi := List.mem_range.mp hk
      change raw+k = r at e
      omega
    exact hPack.trans (setRegs_other _ _ _ r hRaw)

/-- A repeated score read and the following decoded packs retain all 32 actual
FP32 words, including the implicit load wait in the plain softmax path. -/
theorem repeatedScoreQuarterTraceInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (mode : Repeated) (quarter : Fin 4) (stage : Fin 2)
    {g pos : Nat} {t : TState} {ending : Option TState}
    (ht : At t (scorePc mode.round quarter)
      [(scoreReg mode.round quarter,b32 (scoreAddress l g stage quarter))])
    (hBytes : ∀ vals, X.get (g,pos) =
      some ⟨scorePc mode.round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ →
        ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hPresent : ending = none ∨
      (if mode = .unbiased then pos+2 else pos+1) < (X.tr g).length) :
    ∃ u vals, vals.length = 32 ∧
      X.get (g,pos) = some
        ⟨scorePc mode.round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      (mode = .unbiased → X.get (g,pos+1) = some ⟨scorePc mode.round quarter,.tc .waitLd⟩) ∧
      At u (scorePc mode.round quarter+17) [] ∧
      (∀ k < 16, u.regs (repeatedScorePairReg mode quarter k) =
        some (joinValue (vals.getD (2*k) (b32 0)) (vals.getD (2*k+1) (b32 0)))) ∧
      (∀ r, (r < repeatedScoreWordBase mode quarter ∨ repeatedScoreWordBase mode quarter+32 ≤ r) →
        (∀ k < 16, r ≠ repeatedScorePairReg mode quarter k) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if mode = .unbiased then pos+2 else pos+1)) ending ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop pos).take (if mode = .unbiased then 2 else 1)) u := by
  obtain ⟨ds,vals,_,hLength,hCode,hGet,hWait,hRest,hLoadReach⟩ :=
    scoreLoadTraceDecodedInPrefix hp mode.round quarter stage ht.1 ht.2.2.2.1
      ht.2.1 ht.2.2.2.2.1 hRun (hPresent.imp_right (by
        cases mode <;> simp only [Repeated.round,reduceCtorEq,ite_true,ite_false] <;> omega))
  have hD := congrArg Instr.op
    (Option.some.inj (hCode.symm.trans (repeatedScoreDecode mode quarter)))
  have hEq := (Op.tcLd.inj hD).1
  subst ds
  obtain ⟨u,hAt,hLocal,hPack,hFrame⟩ := repeatedScorePackLocal (l := l) (g := g)
    mode quarter ht vals hLength (hBytes vals hGet)
  have hIndex : (if mode.round = .unbiased then pos+2 else pos+1) =
      (if mode = .unbiased then pos+2 else pos+1) := by cases mode <;> rfl
  rw [hIndex] at hRest
  have hMore : (X.tr g).drop (if mode = .unbiased then pos+2 else pos+1) ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hRest
    cases hRest
    exact hPresent.elim (by simp) (fun h => (Nat.not_lt_of_ge (List.drop_eq_nil_iff.mp hEmpty)) h)
  refine ⟨u,vals,hLength,hGet,?_,hAt,hPack,hFrame,hRest.after_local_nonempty hLocal hMore,?_⟩
  · intro h
    subst mode
    exact hWait rfl
  · have hHead (j : Nat) (e : Event) (h : X.get (g,j) = some e) :
        (X.tr g).drop j = e :: (X.tr g).drop (j+1) := by
      have hSome := List.getElem?_eq_some_iff.mp h
      rw [List.drop_eq_getElem_cons hSome.1,hSome.2]
    rw [hHead _ _ hGet]
    have hReached := hLoadReach.append (TraceReach.of_local hLocal)
    rw [List.append_nil] at hReached
    cases mode
    · simpa [Repeated.round] using hReached
    · obtain h := hWait rfl
      rw [hHead _ _ h]
      simpa [Repeated.round] using hReached

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (mode : Repeated)
    (quarter : Fin 4) (stage : Fin 2) {g pos : Nat} {t : TState}
    (ht : At t (scorePc mode.round quarter)
      [(scoreReg mode.round quarter,b32 (scoreAddress l g stage quarter))])
    (hBytes : ∀ vals, X.get (g,pos) =
      some ⟨scorePc mode.round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ →
        ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none)
include hp mode quarter stage ht hBytes hRun

end

private theorem repeatedScoreAddressesSeparate (mode : Repeated) (q r : Fin 4) :
    (scoreReg mode.round r < repeatedScoreWordBase mode q ∨
      repeatedScoreWordBase mode q+32 ≤ scoreReg mode.round r) ∧
    ∀ k : Fin 16, scoreReg mode.round r ≠ repeatedScorePairReg mode q k.val := by
  cases mode <;> revert q r <;> decide

private theorem repeatedScorePairsSeparate (mode : Repeated) (q r : Fin 4) (k : Fin 16)
    (hNe : q ≠ r) :
    (repeatedScorePairReg mode q k.val < repeatedScoreWordBase mode r ∨
      repeatedScoreWordBase mode r+32 ≤ repeatedScorePairReg mode q k.val) ∧
    ∀ j : Fin 16, repeatedScorePairReg mode q k.val ≠ repeatedScorePairReg mode r j.val := by
  cases mode <;> revert q r k <;> decide

/-- One observed score-load event per biased quarter, two per plain quarter. -/
def repeatedScoreStride (mode : Repeated) : Nat := if mode = .unbiased then 2 else 1

private theorem repeatedScoreCursor (mode : Repeated) (q : Fin 4) (start : Nat) :
    ((if mode = .unbiased then start+repeatedScoreStride mode*q.val+2
      else start+repeatedScoreStride mode*q.val+1)) =
      start+repeatedScoreStride mode*(q.val+1) := by
  cases mode <;> simp [repeatedScoreStride] <;> omega

private theorem repeatedScorePcSequence (mode : Repeated) (q : Fin 4) :
    scorePc mode.round q+17 = scorePc mode.round 0+17*(q.val+1) := by
  cases mode <;> fin_cases q <;> decide

private theorem repeatedScorePcOffset (mode : Repeated) (q : Fin 4) :
    scorePc mode.round q = scorePc mode.round 0+17*q.val := by
  have h := repeatedScorePcSequence mode q
  omega

/-- The repeated score loads and packs fill the 64 pairs on their actual common trace. -/
theorem repeatedScoreTraceFromInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (mode : Repeated) (stage : Fin 2) (current : Fin 4)
    {g start : Nat} {t : TState} {ending : Option TState}
    (ht : At t (scorePc mode.round current) [])
    (hRegs : ∀ q : Fin 4, current ≤ q → t.regs (scoreReg mode.round q) =
      some (b32 (scoreAddress l g stage q)))
    (hBytes : ∀ (q : Fin 4) (vs : List Value), current ≤ q →
      X.get (g,start+repeatedScoreStride mode*q.val) =
        some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) vs .s32x32b)⟩ →
      ∀ k < 32, (vs.getD k (b32 0)).bytes = 4)
    (hRun : Run kernel Assumptions.all l g t
      ((X.tr g).drop (start+repeatedScoreStride mode*current.val)) ending)
    (hPresent : ending = none ∨ start+repeatedScoreStride mode*4 < (X.tr g).length) :
    ∃ u, At u (scorePc mode.round 0+68) [] ∧
      (∀ q : Fin 4, current ≤ q → ∃ vs, vs.length = 32 ∧
        X.get (g,start+repeatedScoreStride mode*q.val) =
          some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) vs .s32x32b)⟩ ∧
        (∀ k < 16, u.regs (repeatedScorePairReg mode q k) =
          some (joinValue (vs.getD (2*k) (b32 0)) (vs.getD (2*k+1) (b32 0))))) ∧
      (mode = .unbiased → ∀ q : Fin 4, current ≤ q →
        X.get (g,start+repeatedScoreStride mode*q.val+1) =
          some ⟨scorePc mode.round q,.tc .waitLd⟩) ∧
      (∀ r, (∀ q : Fin 4, current ≤ q →
          (r < repeatedScoreWordBase mode q ∨ repeatedScoreWordBase mode q+32 ≤ r) ∧
          ∀ k : Fin 16, r ≠ repeatedScorePairReg mode q k.val) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+repeatedScoreStride mode*4)) ending ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop (start+repeatedScoreStride mode*current.val)).take
          (repeatedScoreStride mode*(4-current.val))) u := by
  obtain ⟨u,vs,hLen,hGet,hWait,hAt,hPair,hFrame,hTail,hReach⟩ :=
    repeatedScoreQuarterTraceInPrefix hp mode current stage
      (ht.mono ⟨hRegs current le_rfl,trivial⟩) (hBytes current · le_rfl) hRun
      (hPresent.imp_right (fun h => by
        rw [repeatedScoreCursor]
        exact lt_of_le_of_lt (Nat.add_le_add_left
          (Nat.mul_le_mul_left _ current.isLt) _) h))
  rw [repeatedScoreCursor] at hTail
  rw [repeatedScorePcSequence] at hAt
  by_cases hLast : current.val+1 = 4
  · rw [hLast] at hAt hTail
    refine ⟨u,hAt,?_,?_,?_,hTail,?_⟩
    · intro q hQ
      have h : current = q := by apply Fin.ext; have := q.isLt; omega
      subst q
      exact ⟨vs,hLen,hGet,hPair⟩
    · intro hm q hQ
      have h : current = q := by apply Fin.ext; have := q.isLt; omega
      subst q
      exact hWait hm
    · intro r hR
      have h := hR current le_rfl
      exact hFrame r h.1 (fun k hk => h.2 ⟨k,hk⟩)
    · have hOne : 4-current.val = 1 := by omega
      simpa only [hOne,Nat.mul_one,repeatedScoreStride] using hReach
  · let next : Fin 4 := ⟨current.val+1,by have := current.isLt; omega⟩
    have hGt : current < next := by exact Nat.lt_succ_self current.val
    have hNextAt : At u (scorePc mode.round next) [] := by
      rw [repeatedScorePcOffset]
      exact hAt
    have hNext q (hQ : next ≤ q) := (hGt.le.trans hQ)
    have hAddress q (hQ : next ≤ q) : u.regs (scoreReg mode.round q) =
        some (b32 (scoreAddress l g stage q)) := by
      have h := repeatedScoreAddressesSeparate mode current q
      rw [hFrame _ h.1 (fun k hk => h.2 ⟨k,hk⟩)]
      exact hRegs q (hNext q hQ)
    obtain ⟨v,hV,hPairs,hWaits,hKeep,hRest,hReachNext⟩ :=
      repeatedScoreTraceFromInPrefix hp mode stage next hNextAt hAddress
        (fun q vs hQ => hBytes q vs (hNext q hQ)) hTail hPresent
    refine ⟨v,hV,?_,?_,?_,hRest,?_⟩
    · intro q hQ
      by_cases heq : q = current
      · subst q
        refine ⟨vs,hLen,hGet,?_⟩
        intro k hk
        rw [hKeep _ (fun q hQ => repeatedScorePairsSeparate mode current q ⟨k,hk⟩
          (ne_of_lt (hGt.trans_le hQ)))]
        exact hPair k hk
      · exact hPairs q (show next ≤ q from lt_of_le_of_ne hQ (Ne.symm heq))
    · intro hm q hQ
      by_cases heq : q = current
      · subst q
        exact hWait hm
      · exact hWaits hm q (show next ≤ q from lt_of_le_of_ne hQ (Ne.symm heq))
    · intro r hR
      exact (hKeep r (fun q hQ => hR q (hNext q hQ))).trans
        (hFrame r (hR current le_rfl).1 (fun k hk => (hR current le_rfl).2 ⟨k,hk⟩))
    · have hLength : 4-current.val = 1+(4-next.val) := by dsimp [next]; omega
      rw [hLength,Nat.mul_add,Nat.mul_one,List.take_add,List.drop_drop]
      have hPos : start+repeatedScoreStride mode*current.val+repeatedScoreStride mode =
          start+repeatedScoreStride mode*next.val := by dsimp [next]; rw [Nat.mul_succ]; omega
      rw [hPos]
      exact (show TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop (start+repeatedScoreStride mode*current.val)).take
          (repeatedScoreStride mode)) u from hReach).append hReachNext
termination_by 4-current.val
decreasing_by simp; omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (mode : Repeated)
    (stage : Fin 2) (current : Fin 4) {g start : Nat} {t : TState}
    (ht : At t (scorePc mode.round current) [])
    (hRegs : ∀ q : Fin 4, current ≤ q → t.regs (scoreReg mode.round q) =
      some (b32 (scoreAddress l g stage q)))
    (hBytes : ∀ (q : Fin 4) (vs : List Value), current ≤ q →
      X.get (g,start+repeatedScoreStride mode*q.val) =
        some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) vs .s32x32b)⟩ →
      ∀ k < 32, (vs.getD k (b32 0)).bytes = 4)
    (hRun : Run kernel Assumptions.all l g t
      ((X.tr g).drop (start+repeatedScoreStride mode*current.val)) none)
include hp mode stage current ht hRegs hBytes hRun

theorem repeatedScoreTraceFromWithReach :
    ∃ u, At u (scorePc mode.round 0+68) [] ∧
      (∀ q : Fin 4, current ≤ q → ∃ vs, vs.length = 32 ∧
        X.get (g,start+repeatedScoreStride mode*q.val) =
          some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) vs .s32x32b)⟩ ∧
        (∀ k < 16, u.regs (repeatedScorePairReg mode q k) =
          some (joinValue (vs.getD (2*k) (b32 0)) (vs.getD (2*k+1) (b32 0))))) ∧
      (mode = .unbiased → ∀ q : Fin 4, current ≤ q →
        X.get (g,start+repeatedScoreStride mode*q.val+1) =
          some ⟨scorePc mode.round q,.tc .waitLd⟩) ∧
      (∀ r, (∀ q : Fin 4, current ≤ q →
          (r < repeatedScoreWordBase mode q ∨ repeatedScoreWordBase mode q+32 ≤ r) ∧
          ∀ k : Fin 16, r ≠ repeatedScorePairReg mode q k.val) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+repeatedScoreStride mode*4)) none ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop (start+repeatedScoreStride mode*current.val)).take
          (repeatedScoreStride mode*(4-current.val))) u := by
  exact repeatedScoreTraceFromInPrefix hp mode stage current ht hRegs hBytes hRun (.inl rfl)

end

/-- Reassemble the exact observed scalar values in a repeated round's packed score register. -/
theorem repeatedPackedScoreValues {l : Launch} {g : Nat} {t : TState}
    (mode : Repeated) (quarter : Fin 4) (pair : Fin 16)
    {values : List Value} (score : Fin 32 → ℝ)
    (hValues : ∀ word : Fin 32, values[word.val]? = some (.float .f32 (score word)))
    (hReg : t.regs (repeatedScorePairReg mode quarter pair.val) =
      some (joinValue (values.getD (2*pair.val) (b32 0))
        (values.getD (2*pair.val+1) (b32 0)))) :
    let lo : Fin 32 := ⟨2*pair.val,by have := pair.isLt; omega⟩
    let hi : Fin 32 := ⟨2*pair.val+1,by have := pair.isLt; omega⟩
    readERealPair l g t (.reg (repeatedScorePairReg mode quarter pair.val)) =
      some (.ok ((score lo : EReal),(score hi : EReal))) := by
  let lo : Fin 32 := ⟨2*pair.val,by have := pair.isLt; omega⟩
  let hi : Fin 32 := ⟨2*pair.val+1,by have := pair.isLt; omega⟩
  have hLow : values[2*pair.val]? = some (.float .f32 (score lo)) := hValues lo
  have hHigh : values[2*pair.val+1]? = some (.float .f32 (score hi)) := hValues hi
  simp only [List.getD_eq_getElem?_getD, hLow, hHigh, Option.getD_some] at hReg
  exact readERealPair_reg hReg rfl rfl

end PTX.Kernels.TmlFa4Fwd.Softmax
