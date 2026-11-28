-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchButterfly
public import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The first stage of the minimum butterfly agrees between the two halves of a warp

The rescale factor a lane sends at pc 2242 is a function of the words its shuffles of pc 1838
sent and received (`Softmax.Export.alpha_operand`). The shuffles of pc 1838 of two lanes of a warp
that agree modulo 16 are the same shuffles of one ordinal, each lane's received word the other's
sent word (the butterfly's partner), so the words of the rounds before agree up to the order of
the two halves, and the running maximum and the new maximum do not depend on it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof PTX.Flow Softmax.Export

/-- Word lists that agree round by round, each round's pair equal or swapped. -/
inductive Corr : List (Value × Value) → List (Value × Value) → Prop
  | nil : Corr [] []
  | snoc {ps ps' : List (Value × Value)} {p p' : Value × Value} : Corr ps ps' →
      (p = p' ∨ p = (p'.2, p'.1)) → Corr (ps ++ [p]) (ps' ++ [p'])

private theorem corr_mx (m : Value) {p p' : Value × Value} (h : p = p' ∨ p = (p'.2, p'.1)) :
    Lib.mxWord m p.1 p.2 = Lib.mxWord m p'.1 p'.2 := by
  rcases h with rfl | rfl
  · rfl
  · exact Lib.mxWord_swap _ _ _

private theorem corr_m (c : Value) {ps ps' : List (Value × Value)} (h : Corr ps ps') :
    Softmax.Data.mAfter c ps = Softmax.Data.mAfter c ps' := by
  induction h with
  | nil => rfl
  | snoc _ hp ih => rw [Softmax.Data.mAfter_append, Softmax.Data.mAfter_append, ih, corr_mx _ hp]

/-- Agreeing words give the same running maximum and new maximum. -/
theorem Corr.rescale (L : Launch) {ps ps' : List (Value × Value)} (h : Corr ps ps') :
    Softmax.Data.mAfter (Softmax.Data.scaleW L) ps.dropLast =
        Softmax.Data.mAfter (Softmax.Data.scaleW L) ps'.dropLast ∧
      (match ps.getLast? with
        | some p => Lib.mxWord (Softmax.Data.mAfter (Softmax.Data.scaleW L) ps.dropLast) p.1 p.2
        | none => b32 0) =
      (match ps'.getLast? with
        | some p => Lib.mxWord (Softmax.Data.mAfter (Softmax.Data.scaleW L) ps'.dropLast) p.1 p.2
        | none => b32 0) := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | snoc h hp =>
    simp only [List.dropLast_concat, List.getLast?_concat]
    rw [corr_m _ h, corr_mx _ hp]
    exact ⟨rfl, rfl⟩

private theorem count_mono (l : List Event) (a b : Nat) (h : a ≤ b) (p : Event → Bool) :
    (l.take a).countP p ≤ (l.take b).countP p := by
  have := List.take_append_drop a (l.take b)
  rw [List.take_take, Nat.min_eq_left h] at this
  conv => rhs; rw [← this]
  rw [List.countP_append]; omega

/-- Two shuffles of one lane with the same ordinal are the same event. -/
private theorem shfl_index_eq {X : Execution} {g w w' : Nat} {e e' : Event}
    (get : X.get (g, w) = some e) (get' : X.get (g, w') = some e')
    (s : Execution.isShfl e = true) (s' : Execution.isShfl e' = true)
    (cnt : ((X.tr g).take w).countP Execution.isShfl =
      ((X.tr g).take w').countP Execution.isShfl) : w = w' := by
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · have c := count_succ get
    have m := count_mono (X.tr g) (w + 1) w' lt Execution.isShfl
    simp [s] at c
    omega
  · have c := count_succ get'
    have m := count_mono (X.tr g) (w' + 1) w gt Execution.isShfl
    simp [s'] at c
    omega

private theorem partner_lane16 {g : Nat} :
    (g-g%32+(g%32 ^^^ 16))%32=g%32 ^^^ 16 ∧
      (g-g%32+(g%32 ^^^ 16))-(g-g%32+(g%32 ^^^ 16))%32=g-g%32 := by
  have : g%32 ^^^ 16<32 := Nat.xor_lt_two_pow (n:=5) (Nat.mod_lt _ (by decide)) (by decide)
  omega

/-- **The partner of a shuffle of pc 1838** is the shuffle of pc 1838 of the lane 16 away, with
the same ordinal: it sent what this lane received and received what this lane sent. -/
public theorem partner_1838 {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}
    {a recv ok} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (get : X.get (g, k) = some ⟨1838, .shfl .bfly a 16 31 recv ok⟩)
    (lane : g%L.block<128) :
    ∃ j ok', X.get (g-g%32+(g%32 ^^^ 16), j) = some ⟨1838, .shfl .bfly recv 16 31 a ok'⟩ ∧
      ((X.tr (g-g%32+(g%32 ^^^ 16))).take j).countP Execution.isShfl =
        ((X.tr g).take k).countP Execution.isShfl := by
  have hb : L.block=256 := hp.block
  obtain ⟨j,pc',b',c',r',o',got,count⟩ := decision_partner hp hX hf get (Or.inl rfl) lane
  have lane32 : laneOf L g=g%32 := by unfold laneOf; rw [hb]; omega
  rw [lane32] at got count
  rw [bfly_source _ _ (Nat.mod_lt _ (by decide)) (by decide)] at got count
  dsimp only at got count
  obtain ⟨pl, pw⟩ := partner_lane16 (g := g)
  have low : (g-g%32+(g%32 ^^^ 16))%L.block<128 := by
    have : g%32 ^^^ 16<32 := Nat.xor_lt_two_pow (n:=5) (Nat.mod_lt _ (by decide)) (by decide)
    rw [hb] at lane ⊢; omega
  have cta : (g-g%32+(g%32 ^^^ 16))/L.block=g/L.block := by
    have : g%32 ^^^ 16<32 := Nat.xor_lt_two_pow (n:=5) (Nat.mod_lt _ (by decide)) (by decide)
    rw [hb]; omega
  obtain rfl := partner_pc_late hp hX hf get (Or.inl rfl) low cta got rfl count
  obtain ⟨-, rfl, rfl⟩ := shfl5_shape hp hX got
  obtain ⟨j2,pc2,b2,c2,r2,o2,got2,count2⟩ := decision_partner hp hX hf got (Or.inl rfl) low
  have lane32' : laneOf L (g-g%32+(g%32 ^^^ 16))=(g-g%32+(g%32 ^^^ 16))%32 := by
    unfold laneOf; rw [hb]; omega
  have x16 : g%32 ^^^ 16<32 := Nat.xor_lt_two_pow (n:=5) (Nat.mod_lt _ (by decide)) (by decide)
  rw [lane32', pw, pl, bfly_source _ _ x16 (by decide)] at got2 count2
  dsimp only at got2 count2
  have back : (g%32 ^^^ 16) ^^^ 16 = g%32 := by simp [Nat.xor_assoc]
  have back2 : g-g%32+g%32 = g := by omega
  rw [back, back2] at got2 count2
  have same := shfl_index_eq get got2 rfl rfl (by rw [count2, count])
  subst same
  have : (some (Event.mk 1838 (.shfl .bfly a 16 31 recv ok))) =
      some (Event.mk pc2 (.shfl .bfly r' b2 c2 r2 o2)) := get.symm.trans got2
  obtain ⟨-, k2⟩ := Option.some.inj this |> Event.mk.inj
  obtain ⟨-, rfl, -, -, -⟩ := Kind.shfl.inj k2
  exact ⟨j, o', got, count⟩

private theorem wordOf_not_shfl {e : Event} (h : Execution.isShfl e = false) :
    Softmax.Data.wordOf e = [] := by
  obtain ⟨p, k⟩ := e
  cases k <;> simp_all [Softmax.Data.wordOf, Execution.isShfl]

private theorem wordOf_far {e : Event} (h : e.pc ≠ 1838) : Softmax.Data.wordOf e = [] := by
  obtain ⟨p, k⟩ := e
  cases k <;> simp_all [Softmax.Data.wordOf]

/-- The rounds of two lanes of a warp that agree modulo 16, at shuffles of one ordinal: the
shuffle of pc 1838 of one is the other's or its partner's. -/
private theorem pair_pos {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g g' w w' : Nat}
    {mode a b c recv ok} {e' : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (low : g%L.block<128) (warp : g-g%32=g'-g'%32) (lanes : g%32%16=g'%32%16)
    (get : X.get (g, w) = some ⟨1838, .shfl mode a b c recv ok⟩) (get' : X.get (g', w') = some e')
    (s' : Execution.isShfl e' = true)
    (cnt : ((X.tr g).take w).countP Execution.isShfl =
      ((X.tr g').take w').countP Execution.isShfl) :
    e' = ⟨1838, .shfl .bfly a 16 31 recv ok⟩ ∨
      ∃ ok', e' = ⟨1838, .shfl .bfly recv 16 31 a ok'⟩ := by
  obtain ⟨rfl, rfl, rfl⟩ := shfl5_shape hp hX get
  have split : ∀ l<32, ∀ l'<32, l%16=l'%16 → l'=l ∨ l'=l ^^^ 16 := by decide +kernel
  have l1 : g%32<32 := Nat.mod_lt _ (by decide)
  have l2 : g'%32<32 := Nat.mod_lt _ (by decide)
  rcases split _ l1 _ l2 lanes with same | cross
  · have eq : g' = g := by omega
    subst eq
    have idx := shfl_index_eq get get' rfl s' cnt
    subst idx
    exact .inl (Option.some.inj (get.symm.trans get')).symm
  · have eq : g' = g-g%32+(g%32 ^^^ 16) := by
      have : g%32 ^^^ 16<32 := Nat.xor_lt_two_pow (n:=5) l1 (by decide)
      omega
    subst eq
    obtain ⟨j, ok', got, count⟩ := partner_1838 hp hX hf get low
    have idx := shfl_index_eq got get' rfl s' (by rw [count, cnt])
    subst idx
    exact .inr ⟨ok', (Option.some.inj (got.symm.trans get')).symm⟩

/-- The words two lanes of a warp that agree modulo 16 add at shuffles of one ordinal agree. -/
private theorem pair_corr {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g g' w w' : Nat}
    {e e' : Event} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (low : g%L.block<128) (warp : g-g%32=g'-g'%32)
    (lanes : g%32%16=g'%32%16) (get : X.get (g, w) = some e) (get' : X.get (g', w') = some e')
    (s : Execution.isShfl e = true) (s' : Execution.isShfl e' = true)
    (cnt : ((X.tr g).take w).countP Execution.isShfl =
      ((X.tr g').take w').countP Execution.isShfl) :
    (Softmax.Data.wordOf e = [] ∧ Softmax.Data.wordOf e' = []) ∨
      ∃ p p', Softmax.Data.wordOf e = [p] ∧ Softmax.Data.wordOf e' = [p'] ∧
        (p = p' ∨ p = (p'.2, p'.1)) := by
  have hb : L.block=256 := hp.block
  have low' : g'%L.block<128 := by
    rw [hb] at low ⊢
    have h1 : g%32<32 := Nat.mod_lt _ (by decide)
    have h2 : g'%32<32 := Nat.mod_lt _ (by decide)
    have h3 : (g-g%32)%32=0 := by omega
    have h4 : (g-g%32)%256≤96 := by omega
    have h5 : g'=g-g%32+g'%32 := by omega
    omega
  by_cases h : e.pc = 1838
  · obtain ⟨pc, kind⟩ := e
    change pc = 1838 at h
    subst h
    cases kind <;> simp [Execution.isShfl] at s
    rename_i mode a b c recv ok
    rcases pair_pos hp hX hf low warp lanes get get' s' cnt with rfl | ⟨ok', rfl⟩
    · exact .inr ⟨_, _, rfl, rfl, .inl rfl⟩
    · exact .inr ⟨_, _, rfl, rfl, .inr rfl⟩
  · by_cases h' : e'.pc = 1838
    · exfalso
      obtain ⟨pc, kind⟩ := e'
      change pc = 1838 at h'
      subst h'
      cases kind <;> simp [Execution.isShfl] at s'
      rename_i mode a b c recv ok
      rcases pair_pos hp hX hf low' warp.symm lanes.symm get' get s (by rw [cnt]) with
        rfl | ⟨ok', rfl⟩ <;> exact h rfl
    · exact .inl ⟨wordOf_far h, wordOf_far h'⟩

private theorem corr_extend {ps ps' : List (Value × Value)} {w w' : List (Value × Value)}
    (h : Corr ps ps')
    (hw : (w = [] ∧ w' = []) ∨ ∃ p p', w = [p] ∧ w' = [p'] ∧ (p = p' ∨ p = (p'.2, p'.1))) :
    Corr (ps ++ w) (ps' ++ w') := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨p, p', rfl, rfl, hp⟩
  · simpa using h
  · exact .snoc h hp

private theorem words_nil {X : Execution} {g u : Nat}
    (h : ((X.tr g).take u).countP Execution.isShfl = 0) : Softmax.Data.roundWords X g u = [] := by
  unfold Softmax.Data.roundWords
  rw [List.flatMap_eq_nil_iff]
  intro x hx
  exact wordOf_not_shfl (by simpa using (List.countP_eq_zero.mp h x hx))

/-- **The words of two lanes agree**: the words of the rounds before two shuffle ordinals of equal
count are the same round by round, up to the order of the two halves. -/
private theorem words_corr {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g g' : Nat}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (low : g%L.block<128) (warp : g-g%32=g'-g'%32) (lanes : g%32%16=g'%32%16) :
    ∀ n u u', u+u'=n → u≤(X.tr g).length → u'≤(X.tr g').length →
      ((X.tr g).take u).countP Execution.isShfl=((X.tr g').take u').countP Execution.isShfl →
      Corr (Softmax.Data.roundWords X g u) (Softmax.Data.roundWords X g' u') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u u' hn hu hu' cnt
  rcases u with _ | w
  · rw [words_nil (by simp), words_nil (by simpa using cnt.symm)]
    exact Corr.nil
  rcases u' with _ | w'
  · rw [words_nil (by simpa using cnt), words_nil (by simp)]
    exact Corr.nil
  obtain ⟨e, get⟩ : ∃ e, X.get (g, w) = some e :=
    ⟨_, List.getElem?_eq_getElem (show w < (X.tr g).length by omega)⟩
  obtain ⟨e', get'⟩ : ∃ e', X.get (g', w') = some e' :=
    ⟨_, List.getElem?_eq_getElem (show w' < (X.tr g').length by omega)⟩
  have c1 := count_succ get
  have c2 := count_succ get'
  by_cases se : Execution.isShfl e = true
  · by_cases se' : Execution.isShfl e' = true
    · simp only [se, se', ite_true] at c1 c2
      rw [Softmax.Data.roundWords_succ get, Softmax.Data.roundWords_succ get']
      have base := ih (w + w') (by omega) w w' rfl (by omega) (by omega) (by omega)
      exact corr_extend base (pair_corr hp hX hf low warp lanes get get' se se' (by omega))
    · have no' : Execution.isShfl e' = false := by simpa using se'
      simp only [se, no', ite_true, Bool.false_eq_true, ite_false] at c1 c2
      rw [Softmax.Data.roundWords_succ get', wordOf_not_shfl no', List.append_nil]
      exact ih (w + 1 + w') (by omega) (w + 1) w' rfl hu (by omega) (by omega)
  · have no : Execution.isShfl e = false := by simpa using se
    rw [Softmax.Data.roundWords_succ get, wordOf_not_shfl no, List.append_nil]
    simp only [no, Bool.false_eq_true, ite_false] at c1
    exact ih (w + (w' + 1)) (by omega) w (w' + 1) rfl (by omega) hu' (by omega)

/-- **The first shuffle of the butterfly (pc 2242) sends the same factor from the two lanes of a
warp that agree modulo 16**, at one shuffle ordinal: both rows of the warp reduce the same
maxima. -/
theorem alpha_agree {Q : Params} {L : Launch} {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) : StageAgree L X 0 := by
  intro g j a r g' j' a' r' s1 s2 low warp lanes cnt
  have e1 := alpha_operand hp hX s1
  have e2 := alpha_operand hp hX s2
  obtain ⟨_, get1⟩ := s1
  obtain ⟨_, get2⟩ := s2
  have len1 : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp get1).1.le
  have len2 : j' ≤ (X.tr g').length := (List.getElem?_eq_some_iff.mp get2).1.le
  have C := words_corr hp hX hf low warp (by simpa using lanes) _ j j' rfl len1 len2 cnt
  obtain ⟨hm, hmx⟩ := C.rescale L
  rw [e1, e2]
  exact congrArg₂ (Softmax.Data.alphaWord (Softmax.Data.scaleW L)) hm hmx

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
