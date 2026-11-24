-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocObjectWaiting
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! Appending an object/control instruction does not perform its independent memory
operations. Existing asynchronous stages retain their issuer and byte contents. -/
namespace PTX
open AsyncCopy
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- The stage of a linear operation that the old snapshot records has an old issuing
instruction, so an appended event does not change which operation issued it. -/
theorem snoc_copy_of_nonempty (ht : TmaOk X) {i : EvId} {s : Spec}
    (hp : nonempty (X.async.copies i)) : (X.snoc g e r).Copy i s ↔ X.Copy i s := by
  obtain ⟨s', hs, _⟩ := ht.1 i hp
  obtain ⟨pc, he⟩ := issuedBy_some.mp hs
  simp only [Execution.Copy, snoc_get_old (len_of_get he)]

theorem snoc_copy_lift {i : EvId} {s : Spec} (hc : X.Copy i s) : (X.snoc g e r).Copy i s := by
  obtain ⟨pc, hp⟩ := hc
  exact ⟨pc, Execution.le_get le_snoc hp⟩

theorem snoc_kind_ne_iff {v : EvId} {k : Kind} (hk : e.kind ≠ k) :
    (∃ pc, (X.snoc g e r).get v = some ⟨pc, k⟩) ↔ ∃ pc, X.get v = some ⟨pc, k⟩ := by
  constructor
  · rintro ⟨pc, hp⟩
    rw [snoc_get] at hp
    split_ifs at hp
    · exact False.elim (hk (congrArg Event.kind (Option.some.inj hp)))
    · exact ⟨pc, hp⟩
  · rintro ⟨pc, hp⟩
    exact ⟨pc, by rw [snoc_get_old (len_of_get hp)]; exact hp⟩

theorem snoc_memReads_control (hv : EffectValidity L X)
    (hk : ∀ k, e.kind ≠ .tc k) (hrd : ∀ a bs, e.kind ≠ .rd a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    {v : Ref} {a : Acc} {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads v a bs ↔ X.MemReads v a bs := by
  cases v with
  | thread i =>
    exact or_congr (snoc_kind_ne_iff (hrd a bs))
      (exists_congr fun n => snoc_kind_ne_iff (hrmw a bs n))
  | async i p =>
    cases p <;> simp only [Execution.MemReads]
    case readCopy =>
      constructor
      · rintro ⟨s, raw, hc, hsrc, hraw, hbs⟩
        exact ⟨s, raw, (snoc_copy_of_nonempty hv.tma ⟨.read .copy, by
          simp [present, ← snoc_async (X := X) (g := g) (e := e) (r := r),
            hraw]⟩).mp hc, hsrc, hraw, hbs⟩
      · rintro ⟨s, raw, hc, hsrc, hraw, hbs⟩
        exact ⟨s, raw, snoc_copy_lift hc, hsrc, hraw, hbs⟩
    case oldElem j =>
      constructor
      · rintro ⟨s, rr, raw, hc, hw, hel, hraw, hbs⟩
        exact ⟨s, rr, raw, (snoc_copy_of_nonempty hv.tma ⟨.old (.elem j), by
          simp [present, ← snoc_async (X := X) (g := g) (e := e) (r := r),
            hraw]⟩).mp hc, hw, hel, hraw, hbs⟩
      · rintro ⟨s, rr, raw, hc, hw, hel, hraw, hbs⟩
        exact ⟨s, rr, raw, snoc_copy_lift hc, hw, hel, hraw, hbs⟩
    case mmaRead => simp only [snoc_mmaRead hk]
    case readLoad x y k =>
      constructor
      · rintro ⟨o,addr,b,ho,hissue,hl,hb,hn,hbs⟩
        obtain ⟨addr',pc,hp⟩ := (hv.tensor i o ho).1
        have hi' : X.TensorIssue i addr o.spec := by
          simpa only [Execution.TensorIssue,snoc_get_old (len_of_get hp)] using hissue
        exact ⟨o,addr,b,ho,hi',hl,hb,hn,hbs⟩
      · rintro ⟨o,addr,b,ho,⟨pc,hp⟩,hl,hb,hn,hbs⟩
        exact ⟨o,addr,b,ho,⟨pc,Execution.le_get le_snoc hp⟩,hl,hb,hn,hbs⟩
    case readStore x y k =>
      constructor
      · rintro ⟨o,addr,b,ho,hissue,hl,hb,hn,hbs⟩
        obtain ⟨addr',pc,hp⟩ := (hv.store i o ho).1
        have hi' : X.TensorStoreIssue i addr o.spec := by
          simpa only [Execution.TensorStoreIssue,snoc_get_old (len_of_get hp)] using hissue
        exact ⟨o,addr,b,ho,hi',hl,hb,hn,hbs⟩
      · rintro ⟨o,addr,b,ho,⟨pc,hp⟩,hl,hb,hn,hbs⟩
        exact ⟨o,addr,b,ho,⟨pc,Execution.le_get le_snoc hp⟩,hl,hb,hn,hbs⟩
    case oldStore x y k =>
      constructor
      · rintro ⟨o,addr,b,ho,hissue,hred,hl,hb,hn,hbs⟩
        obtain ⟨addr',pc,hp⟩ := (hv.store i o ho).1
        have hi' : X.TensorStoreIssue i addr o.spec := by
          simpa only [Execution.TensorStoreIssue,snoc_get_old (len_of_get hp)] using hissue
        exact ⟨o,addr,b,ho,hi',hred,hl,hb,hn,hbs⟩
      · rintro ⟨o,addr,b,ho,⟨pc,hp⟩,hred,hl,hb,hn,hbs⟩
        exact ⟨o,addr,b,ho,⟨pc,Execution.le_get le_snoc hp⟩,hred,hl,hb,hn,hbs⟩

theorem snoc_memWrites_control (hv : EffectValidity L X)
    (hwr : ∀ a bs, e.kind ≠ .wr a bs) (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    {v : Ref} {a : Acc} {bs : List Byte} :
    (X.snoc g e r).MemWrites v a bs ↔ X.MemWrites v a bs := by
  cases v with
  | thread i =>
    exact or_congr (snoc_kind_ne_iff (hwr a bs))
      (exists_congr fun o => snoc_kind_ne_iff (hrmw a o (some bs)))
  | async i p =>
    cases p <;> simp only [Execution.MemWrites]
    case writeCopy =>
      constructor
      · rintro ⟨s, hc, hw, hd, hraw⟩
        exact ⟨s, (snoc_copy_of_nonempty hv.tma ⟨.write .copy, by
          simp [present, ← snoc_async (X := X) (g := g) (e := e) (r := r),
            hraw]⟩).mp hc, hw, hd, hraw⟩
      · rintro ⟨s, hc, hw, hd, hraw⟩
        exact ⟨s, snoc_copy_lift hc, hw, hd, hraw⟩
    case writeElem j =>
      constructor
      · rintro ⟨s, hc, hel, hraw⟩
        exact ⟨s, (snoc_copy_of_nonempty hv.tma ⟨.write (.elem j), by
          simp [present, ← snoc_async (X := X) (g := g) (e := e) (r := r),
            hraw]⟩).mp hc, hel, hraw⟩
      · rintro ⟨s, hc, hel, hraw⟩
        exact ⟨s, snoc_copy_lift hc, hel, hraw⟩
    case writeLoad x y k =>
      constructor
      · rintro ⟨o,addr,b,ho,hissue,hl,hb,hn,hbs,hac,hr,hs⟩
        obtain ⟨addr',pc,hp⟩ := (hv.tensor i o ho).1
        have hi' : X.TensorIssue i addr o.spec := by
          simpa only [Execution.TensorIssue,snoc_get_old (len_of_get hp)] using hissue
        exact ⟨o,addr,b,ho,hi',hl,hb,hn,hbs,hac,hr,hs⟩
      · rintro ⟨o,addr,b,ho,⟨pc,hp⟩,hl,hb,hn,hbs,hac,hr,hs⟩
        exact ⟨o,addr,b,ho,⟨pc,Execution.le_get le_snoc hp⟩,hl,hb,hn,hbs,hac,hr,hs⟩
    case writeStore x y k =>
      constructor
      · rintro ⟨o,addr,b,ho,hissue,hl,hb,hn,hbs,hac,hr,hs⟩
        obtain ⟨addr',pc,hp⟩ := (hv.store i o ho).1
        have hi' : X.TensorStoreIssue i addr o.spec := by
          simpa only [Execution.TensorStoreIssue,snoc_get_old (len_of_get hp)] using hissue
        exact ⟨o,addr,b,ho,hi',hl,hb,hn,hbs,hac,hr,hs⟩
      · rintro ⟨o,addr,b,ho,⟨pc,hp⟩,hl,hb,hn,hbs,hac,hr,hs⟩
        exact ⟨o,addr,b,ho,⟨pc,Execution.le_get le_snoc hp⟩,hl,hb,hn,hbs,hac,hr,hs⟩
    case writeCta c =>
      constructor
      · rintro ⟨spec,targets,hissue,hmem,hw⟩
        obtain ⟨spec',targets',pc,hp⟩ := hv.clc.2.2.1 i (.inr (.inl ⟨c,hw.1⟩))
        have hi' : X.ClcIssue i spec targets := by
          simpa only [Execution.ClcIssue,snoc_get_old (len_of_get hp)] using hissue
        exact ⟨spec,targets,hi',hmem,hw⟩
      · rintro ⟨spec,targets,⟨pc,hp⟩,hmem,hw⟩
        exact ⟨spec,targets,⟨pc,Execution.le_get le_snoc hp⟩,hmem,hw⟩

/-- A source/object event cannot erase or reinterpret an already observed memory read. -/
theorem snoc_history_rf {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X)
    (hk : ∀ k, e.kind ≠ .tc k) (hrd : ∀ a bs, e.kind ≠ .rd a bs)
    (hwr : ∀ a bs, e.kind ≠ .wr a bs) (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (records : Loc → List (MBarrier.Record Ref)) :
    RfWf mem0 (X.snocHistory g e r records) := by
  intro v a bs hv
  have hvX := (snoc_memReads_control (X := X) (g := g) (r := r) hX.effectValidity hk hrd
    hrmw).mp hv
  have hn : v ≠ .thread (g, (X.tr g).length) := by
    intro heq
    rw [heq] at hvX
    rcases hvX with ⟨pc, he⟩ | ⟨_, pc, he⟩ <;>
    · have hh := len_of_get he
      simp at hh
  obtain ⟨hlen, hs⟩ := hX.rf v a bs hvX
  refine ⟨hlen, fun k hk' => ?_⟩
  change (match (if v = .thread (g, (X.tr g).length) then r k else X.rf v k) with
    | none => _
    | some w => _)
  rw [ite_eq_right hn]
  have hh := hs k hk'
  cases hrf : X.rf v k with
  | none => simp only [hrf] at hh ⊢; exact hh
  | some w =>
    rw [hrf] at hh
    obtain ⟨a', bytes, hw, hc, hb⟩ := hh
    exact ⟨a', bytes, (snoc_memWrites_control (X := X) (g := g) (r :=
      r) hX.effectValidity hwr hrmw).mpr hw, hc, hb⟩

end
end
end PTX
