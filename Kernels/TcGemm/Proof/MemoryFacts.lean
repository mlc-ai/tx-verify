-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Values

@[expose] public section

/-! # The memory branches of `Unsafe`

*Allocation* (`no_unalloc`): every access is to an input (`A`, `B`), the output `D` or the shared
variables, all allocated by `Pre`. No access overlaps an mbarrier (`intent_mbar_disjoint`).

*Order* (`conflict_order`): the only overlapping write and read are the address store and the
address reads, ordered by the first barrier (`tslot_intent_order`), and the copies' writes and
the MMA's operand reads, ordered through the observing poll of `bar0` (`mma_intent_copy_order`);
two overlapping writes are one (`writes_overlap_same`). So there is no race and no mixed-size
conflict (`no_race`, `no_mixed`). Every shared access and every mbarrier operation is in CTA 0,
the CTA of every thread (`intent_local`, `object_local`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier
noncomputable section

/-- Every byte of A's packed storage corresponds to a matrix element. -/
theorem offA_onto {q : Nat} (hq : q < 4096) : ∃ i < 128, ∃ k < 32, offA i k = q :=
  ⟨q / 256 * 8 + q / 16 % 8, by omega, q % 16 + 16 * (q / 128 % 2), by omega, by unfold offA; omega⟩

theorem offB_onto {q : Nat} (hq : q < 256) : ∃ k < 32, ∃ j < 8, offB k j = q :=
  ⟨q % 16 + 16 * (q / 128), by omega, q / 16 % 8, by omega, by unfold offB; omega⟩

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
section
variable (hpre : Pre L A B D a b mem0)
include hpre

theorem inputA_alloc {l : Loc} (hc : ({ loc := gA A, size := 4096 } : Acc).Covers l) : mem0 l ≠ none
    := by
  obtain ⟨sp, cta, addr⟩ := l
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  obtain ⟨i, hi, k, hk, he⟩ := offA_onto (q := addr - A) (by simp [gA] at hlo hhi; omega)
  obtain ⟨byte, hm, _⟩ := hpre.inputA i hi k hk
  simp only [gA] at hlo
  rw [he, Nat.add_sub_of_le hlo] at hm
  change mem0 ⟨.global, 0, addr⟩ ≠ none
  rw [hm]; nofun

theorem inputB_alloc {l : Loc} (hc : ({ loc := gB B, size := 256 } : Acc).Covers l) : mem0 l ≠ none
    := by
  obtain ⟨sp, cta, addr⟩ := l
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  obtain ⟨k, hk, j, hj, he⟩ := offB_onto (q := addr - B) (by simp [gB] at hlo hhi; omega)
  obtain ⟨byte, hm, _⟩ := hpre.inputB k hk j hj
  simp only [gB] at hlo
  rw [he, Nat.add_sub_of_le hlo] at hm
  change mem0 ⟨.global, 0, addr⟩ ≠ none
  rw [hm]; nofun

theorem shared_alloc {l : Loc} (hc : ({ loc := sA L.sharedBase, size := 4372 } : Acc).Covers l) :
    mem0 l ≠ none := by
  obtain ⟨sp, cta, addr⟩ := l
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have hm := hpre.shared (addr - L.sharedBase) (by simp [sA] at hlo hhi; omega)
  simp only [sA] at hlo
  simpa [sA, Nat.add_sub_of_le hlo] using hm

theorem output_alloc {l : Loc} (hc : ({ loc := gD D 0, size := 4096 } : Acc).Covers l) : mem0 l ≠
    none := by
  obtain ⟨sp, cta, addr⟩ := l
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have hm := hpre.output (addr - D) (by simp [gD] at hlo hhi; omega)
  have hlo' : D ≤ addr := by simpa [gD] using hlo
  simpa [gD, Nat.add_sub_of_le hlo'] using hm

end
section
variable (hpre : Pre L A B D a b mem0) (hW : Wit A B D L.sharedBase X P m u)
include hpre hW

theorem intent_alloc {e : Ref} {acc : Acc} {w : Bool} {l : Loc}
    (he : X.Intent e acc w) (hc : acc.Covers l) : mem0 l ≠ none := by
  cases w with
  | false =>
    rcases hW.read_intent he with ⟨g, hg, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨k, hk, q, hq, _, hfoot⟩ | ⟨k, hk, q, hq, _, hfoot⟩
    all_goals try (obtain ⟨loc,size,acq,rel,scope⟩ := acc; rcases hfoot with ⟨rfl,rfl⟩)
    · apply shared_alloc hpre
      simp only [Acc.Covers, Loc.InRange, tslot, sA] at hc ⊢
      exact ⟨hc.1, hc.2.1, by omega, by omega⟩
    · exact inputA_alloc hpre hc
    · exact inputB_alloc hpre hc
    all_goals
      apply shared_alloc hpre
      simp only [Acc.Covers, Loc.InRange, Loc.at, sA, sB] at hc ⊢
      exact ⟨hc.1, hc.2.1, by omega, by omega⟩
  | true =>
    rcases hW.write_intent he with ⟨_, rfl⟩ | ⟨g, hg, k, hk, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · apply shared_alloc hpre
      simp only [Acc.Covers, Loc.InRange, tslot, sA] at hc ⊢
      exact ⟨hc.1, hc.2.1, by omega, by omega⟩
    · apply output_alloc hpre
      simp only [Acc.Covers, Loc.InRange, stAcc, gD, Nat.mul_zero, Nat.add_zero] at hc ⊢
      exact ⟨hc.1, hc.2.1, by omega, by omega⟩
    all_goals
      apply shared_alloc hpre
      simp only [Acc.Covers, Loc.InRange, sA, sB] at hc ⊢
      exact ⟨hc.1, hc.2.1, by omega, by omega⟩

theorem no_unalloc : ¬ Unalloc mem0 X := by
  rintro (⟨e, acc, l, ht, hc, hn⟩ | ⟨e, mb, l, hu, hc, hn⟩)
  · rcases ht with ⟨w, he⟩ | ⟨i, bs, _, hnc⟩
    · exact intent_alloc hpre hW he hc hn
    · exact hW.no_nc hnc
  · refine shared_alloc hpre ?_ hn
    rcases hW.uses_mbar hu with rfl | rfl <;>
      simp only [Acc.Covers, Loc.InRange, bar0, bar1, sA] at hc ⊢ <;>
      exact ⟨hc.1, hc.2.1, by omega, by omega⟩

omit hpre in
/-- Neither ordinary data accesses nor asynchronous operands overlap either object. -/
theorem intent_mbar_disjoint {e : Ref} {acc : Acc} {w : Bool} {l mb : Loc}
    (he : X.Intent e acc w) (hc : acc.Covers l)
    (hm : mb = bar0 L.sharedBase ∨ mb = bar1 L.sharedBase) :
    ¬ ({ loc := mb, size := 8 } : Acc).Covers l := by
  intro hmb
  have hspace : acc.loc.space = mb.space := hc.1.symm.trans hmb.1
  cases w with
  | false =>
    rcases hW.read_intent he with ⟨g, hg, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨k, hk, q, hq, _, hfoot⟩ | ⟨k, hk, q, hq, _, hfoot⟩ <;> rcases hm with rfl | rfl
    all_goals try (obtain ⟨loc,size,acq,rel,scope⟩ := acc; rcases hfoot with ⟨rfl,rfl⟩)
    all_goals try (simp [Loc.at, gA, gB, sA, sB, tslot, bar0, bar1] at hspace)
    all_goals simp [Acc.Covers, Loc.InRange, Loc.at, sA, sB, tslot, bar0, bar1] at hc hmb; omega
  | true =>
    rcases hW.write_intent he with ⟨_, rfl⟩ | ⟨g, hg, k, hk, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases hm with rfl | rfl
    all_goals try (simp [stAcc, sA, sB, tslot, bar0, bar1] at hspace)
    all_goals simp [Acc.Covers, Loc.InRange, sA, sB, tslot, bar0, bar1] at hc hmb; omega
end

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

theorem intent_index {e : Ref} {acc : Acc} {w : Bool} (he : X.Intent e acc w) :
    e.issuer.1 < 128 ∧ e.issuer.2 < m e.issuer.1 := by
  obtain ⟨ev, hi⟩ := intent_issuer he
  obtain ⟨hg, ⟨hj, _⟩ | ⟨_, pc, f, _, hu⟩⟩ := hW.get hi
  · exact ⟨hg, hj⟩
  · rw [u_nil hpre hX hW hg] at hu; cases hu

theorem tslot_intent_order {g : Nat}
    (hr : X.Intent (.thread (g, hd g)) { loc := tslot L.sharedBase, size := 4 } false) :
    baseCausality L X (0, 1) (g, hd g) := by
  obtain ⟨hg, hm⟩ := intent_index hpre hX hW hr
  simp only [Ref.issuer] at hg hm
  have hm0 := (rd_val hpre hX hW hg hm).1
  have hpos := hd_pos (g := g)
  have hlen := hW.length g hg
  exact sync0 hpre hX hW (by decide) hg (by decide) (by change 8 < m 0; exact hm0) le_rfl
    (by omega)

/-- An issued MMA lies after a successful operand-copy wait in this kernel. -/
theorem mma_intent_copy_order {p : Part} {acc : Acc}
    (hr : X.Intent (.async (0, hd 0 + 2 + (P 0).n0) p) acc false)
    {copy : EvId} {s : AsyncCopy.Spec} {l : Loc} (hc : copy = (0, 6) ∨ copy = (0, 7))
    (hi : X.Copy copy s) (hcover : s.dst.Covers l) (ha : acc.Covers l) :
    modelCausality L X l (.async copy (.write .copy)) (.async (0, hd 0 + 2 + (P 0).n0) p) := by
  have hidx := (intent_index hpre hX hW hr).2
  change hd 0 + 2 + (P 0).n0 < m 0 at hidx
  have hw : X.get (0, hd 0 + 1 + (P 0).n0) = some (wait0E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_w0t]
  obtain ⟨hA, hB⟩ := wait_observes_copies hX hW hw
  set ws : MbarScope := .cta
  have ho : AsyncObserved X copy (.notify .copy) (0, hd 0 + 1 + (P 0).n0) true ws := by
    rcases hc with rfl | rfl
    · exact hA
    · exact hB
  obtain ⟨ev, hev⟩ := intent_issuer hr
  have hsm : ScopesMeet L .cluster copy.1 ws (0, hd 0 + 1 + (P 0).n0).1 :=
    .of_sameCta
      (by have ht := threads_eq hpre; rcases hc with rfl | rfl <;> exact ⟨by omega, by omega, rfl⟩)
  exact
    ⟨.inl (by have ht := threads_eq hpre; rcases hc with rfl | rfl <;> exact ⟨by omega, by omega,
    rfl⟩),
    .direct ⟨⟨s.dst, true, ⟨rfl, s, hi, (hW.copy_spec hi).2.1, rfl⟩, hcover⟩, ⟨acc, false, hr, ha⟩,
      .inl ⟨(0, hd 0+1+ (P 0).n0),
        .inr ⟨ws, by obtain ⟨n, mb, hn, hwo⟩ := ho; exact ⟨n, mb, .inl hn, hwo⟩, hsm⟩,
        po_baseCausality (by omega) (len_of_get hev) (by rw [hw]; rfl)⟩ ⟩ ⟩

omit hpre hX in
/-- Overlapping writes in this kernel are the same operation. This fact is not a Core
restriction and is proved using both ordinary and asynchronous write intents. -/
theorem writes_overlap_same {e f : Ref} {aa bb : Acc} {l : Loc}
    (he : X.Intent e aa true) (hf : X.Intent f bb true) (ha : aa.Covers l) (hb : bb.Covers l) : e =
      f := by
  have hspace : aa.loc.space = bb.loc.space := ha.1.symm.trans hb.1
  rcases hW.write_intent he with ⟨rfl, rfl⟩ | ⟨g, hg, k, hk, rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hW.write_intent hf with ⟨rfl, rfl⟩ | ⟨h, hh, j, hj, rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals try rfl
  all_goals try (simp [tslot, sA, sB, stAcc] at hspace)
  all_goals try (simp [Acc.Covers, Loc.InRange, tslot, sA, sB, stAcc] at ha hb; omega)
  simp only [Acc.Covers, Loc.InRange, stAcc] at ha hb
  have hgh : g = h := by omega
  subst h
  have hkj : k = j := by omega
  subst j
  rfl

/-- Only tslot publication and copy-to-MMA consumption can overlap a write and read. -/
theorem write_read_order {e f : Ref} {aa bb : Acc} {l : Loc}
    (he : X.Intent e aa true) (hf : X.Intent f bb false) (ha : aa.Covers l) (hb : bb.Covers l) :
    modelCausality L X l e f := by
  have hspace : aa.loc.space = bb.loc.space := ha.1.symm.trans hb.1
  have hdA := hpre.disjointA
  have hdB := hpre.disjointB
  rcases hW.write_intent he with ⟨rfl, rfl⟩ | ⟨g, hg, k, hk, rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hW.read_intent hf with ⟨h, hh, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨j, hj, q, hq, rfl, hfoot⟩ | ⟨j, hj, q, hq, rfl, hfoot⟩
  all_goals try (obtain ⟨loc,size,acq,rel,scope⟩ := bb; rcases hfoot with ⟨rfl,rfl⟩)
  all_goals try (simp [Loc.at, tslot, sA, sB, stAcc, gA, gB] at hspace)
  all_goals try
    (simp [Acc.Covers, Loc.InRange, Loc.at, tslot, sA, sB, stAcc, gA, gB] at ha hb; omega)
  · exact .inl (tslot_intent_order hpre hX hW hf)
  · obtain ⟨_, s, hi, -, hd⟩ := he
    exact mma_intent_copy_order hpre hX hW hf (.inl rfl) hi (hd ▸ ha) hb
  · obtain ⟨_, s, hi, -, hd⟩ := he
    exact mma_intent_copy_order hpre hX hW hf (.inr rfl) hi (hd ▸ ha) hb

theorem conflict_order {e f : Ref} {aa bb : Acc} {l : Loc}
    (hc : Conflict X e f aa bb) (ha : aa.Covers l) (hb : bb.Covers l) :
    modelCausality L X l e f ∨ modelCausality L X l f e := by
  obtain ⟨hne, we, wf, he, hf, hw, _⟩ := hc
  cases we <;> cases wf
  · simp at hw
  · exact .inr (write_read_order hpre hX hW hf he hb ha)
  · exact .inl (write_read_order hpre hX hW he hf ha hb)
  · exact (hne (writes_overlap_same hW he hf ha hb)).elim

theorem no_race : ¬ Race L X := by
  rintro ⟨e,f,aa,bb,l,hc,hfoot,ha,-,hn,hm,-⟩
  exact (conflict_order hpre hX hW hc ha ((hfoot.covers l).mp ha)).elim
    (fun edge => hn (.direct edge)) (fun edge => hm (.direct edge))

theorem strong_ordered : StrongOrdered L X :=
  StrongOrdered.of_conflicts fun _ _ _ _ _ hc ha hb => conflict_order hpre hX hW hc ha hb

theorem no_mixed : ¬ Mixed L X := by
  rintro ⟨e, f, aa, bb, l, hc, _, ha, hb, hn, hm⟩
  exact (conflict_order hpre hX hW hc ha hb).elim
    (fun edge => hn (.direct edge)) (fun edge => hm (.direct edge))

/-- Every shared access is in its issuer's CTA, CTA 0. -/
theorem intent_local {e : Ref} {acc : Acc} {w : Bool} (he : X.Intent e acc w)
    (hs : acc.loc.space = .shared) : acc.loc.cta = e.issuer.1 / L.block := by
  have hi := (intent_index hpre hX hW he).1
  rw [cta_zero hpre hi]
  cases w with
  | true =>
    rcases hW.write_intent he with ⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    all_goals rfl
  | false =>
    rcases hW.read_intent he with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨_, _, _, _, _, hfoot⟩ | ⟨_, _, _, _, _, hfoot⟩
    all_goals first | rfl | (rw [hfoot.1]; rfl)

/-- Every mbarrier operation is on an object of its issuer's CTA, CTA 0. -/
theorem object_local {mb : Loc} {e : Ref} {act : Action}
    (ha : objectAction X X.async mb e = some act) : mb.cta = e.issuer.1 / L.block := by
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 mb).2.2 _ _ ha
  have hi := (object_record_issuer_lt hX hW hr).1
  rw [hid] at hi
  rw [cta_zero hpre hi]
  rcases object_action_cases hW ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl

omit hX in
/-- Every commit targets a barrier of its issuer's CTA, CTA 0. -/
theorem commit_local {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {mb : Loc}
    (hc : X.Commit i s) (ht : TcCommit.target s rank = some mb) : mb.cta = i.1 / L.block := by
  obtain ⟨pc, hp⟩ := hc
  obtain ⟨g, j⟩ := i
  obtain ⟨hg, -, rfl, -, rfl⟩ := hW.commit hp
  obtain ⟨-, rfl⟩ := commitSpec_target ht
  rw [cta_zero hpre hg]; rfl

end

end

end PTX.Kernels.TcGemm.Proof
