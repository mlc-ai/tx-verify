-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Ref.Fence
public import Kernels.InklingRelDecode.Proof2.Ref.Alloc
public import Kernels.InklingRelDecode.Proof2.Ref.WriteCta
public import Lemmas.Kernel.Source.ProtectedRead
public import Lemmas.Order.ReadLast

@[expose] public section

/-! # The base word's read returns column 0 (`BaseRead`), and the following without a premise

The startup's load of the CTA's shared base (pc 13) reads the word the allocation's store of the
CTA's thread 0 wrote, the 32-bit word 0 (`early_write`), by `read_of_last_write`:

* the store is before the read by barrier 0's first instance (`bar0_before`); the CTA's thread 0
  made it before its own first barrier-0 event, which the reader's first barrier-0 event
  synchronizes with (`writer`);
* every other store of the word's bytes is after the read: a store before its thread's second
  barrier-0 event is the allocation's store itself (`early_write`), a later one is after the read
  by barrier 0's second instance (`bar0_before`); a thread's stores are in its own CTA
  (`thread_write_cta`);
* every asynchronous write of the bytes is a tensor copy into the CTA (no other asynchronous write
  is in the code), whose issue is after a proxy fence of the CTA (`issue_fence`), itself after two
  barrier-0 events of its thread and so after the read (`ProxyBefore`).

Everything used is the first stage of the following (`Ref/Stage1.lean`, `Ref/Early.lean`), which
needs no source of the base word. So `good_all` holds without a premise (`good_all'`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem kernel_noBulk : kernel.code.all (fun ins => !bulkOp ins.op) = true := by decide +kernel
theorem kernel_noTensorStore : kernel.code.all (fun ins => !tensorStoreOp ins.op) = true := by
  decide +kernel
theorem kernel_noClc : kernel.code.all (fun ins => !clcOp ins.op) = true := by decide +kernel

/-- **An asynchronous write of the kernel is a tensor copy's.** -/
theorem async_copy (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {e : Event}
    {a : Acc} (he : X.get i = some e) (hw : WriteOf e a) (hnt : ¬ ThreadWrite e) :
    ∃ pc a' s, e = ⟨pc, .tensorIssue a' s⟩ ∧ ∃ x y k, TensorCopy.writeLoc s x y k = some a.loc := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | tensorIssue a' s => exact ⟨pc, a', s, rfl, hw⟩
  | wr a' bs => exact absurd trivial hnt
  | rmw a' old new =>
    cases new with
    | none => exact hw.elim
    | some _ => exact absurd trivial hnt
  | copy s =>
    exact absurd ⟨s, rfl⟩ (no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
      (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk) kernel_noBulk he)
  | tensorStore a' s =>
    exact absurd ⟨a', s, rfl⟩ (no_kind_of_code hX tensorStoreOp
      (fun k => ∃ a s, k = .tensorStore a s) (fun _ ⟨_, _, h⟩ => by cases h)
      (fun hf ⟨_, _, hk⟩ => fires_tensorStore_op hf hk) kernel_noTensorStore he)
  | clcIssue s tg =>
    exact absurd ⟨s, tg, rfl⟩ (no_kind_of_code hX clcOp
      (fun k => ∃ s tg, k = .clcIssue s tg) (fun _ ⟨_, _, h⟩ => by cases h)
      (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk) kernel_noClc he)
  | _ => exact hw.elim

/-- **A tensor copy writes its issuer's CTA.** -/
theorem copy_cta (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h j pc a : Nat}
    {s : TensorCopy.Spec} (he : X.get (h, j) = some ⟨pc, .tensorIssue a s⟩) {x y k : Nat}
    {l : Loc} (hl : TensorCopy.writeLoc s x y k = some l) : l.cta = h / L.block := by
  have hbase : s.sharedBase.cta = h / L.block := by
    rcases Frame.fired (C := thread Q L) (fun g hg => thread_sound hp hg) hX he with
      ⟨σ, o', -, hF⟩ | ⟨-, pc'', f, hf⟩
    · rcases Code.fired_op hF with ⟨pc'', f, hf⟩ | ⟨t, ins, hc, hf⟩
      · cases hf
      · have hop : tensorOp ins.op = true := by
          cases hq : tensorOp ins.op
          · exact (fires_notTensor (eventTmpl_notTensor hq) hf a s rfl).elim
          · rfl
        have hl' : Proof.Interface.localCopyOp ins.op = true := by
          cases hl' : Proof.Interface.localCopyOp ins.op
          · have := OpPcsFast.mem Proof.Interface.kernel_copy_local hc (by simp [hop, hl'])
            simp at this
          · rfl
        exact Proof.Interface.fires_copy_base hl' hf rfl
    · cases hf
  simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hl
  obtain ⟨slot, -, rfl⟩ := hl
  exact hbase

/-- A proxy fence is after its thread's second barrier-0 event. -/
theorem fence_c0 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {f jf pc : Nat}
    (he : X.get (f, jf) = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩) :
    2 ≤ c0 X f jf := by
  by_contra hlt
  obtain ⟨s, n, -, hs, -, hev⟩ := early_at (Q := Q) hp hX he (by simp) (by omega)
  obtain ⟨site, tm, x, bw⟩ := s
  simp only at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [Startup.Ev] at hev
  · cases hev
  · obtain ⟨_, _, h⟩ := hev; cases h
  · cases hev
  · obtain ⟨_, _, h, _⟩ := hev; cases h
  · cases hev

/-- **The allocation's store**: once a thread of a CTA has passed its first barrier-0 event, the
CTA's thread 0 stored the word 0 at the CTA's shared base as its second event. -/
theorem writer (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    (hg : g < L.threads) (hk : k < (X.tr g).length) (hc : c0 X g k = 1) :
    (∃ pcw, X.get (g / L.block * L.block, 1) = some ⟨pcw,
      .wr { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } (b32 0).toBytes⟩) ∧
      c0 X (g / L.block * L.block) 2 = 0 := by
  have hbk : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg0t : g / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hcta : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  have hw0 : g / L.block * L.block % L.block = 0 := Nat.mul_mod_left _ _
  -- the reader's first barrier-0 event
  obtain ⟨j0, hj0, ev, hget0, hb0, hc0⟩ := nth_of_count (X := X) (g := g) (q := 0) (k := k)
    (P := Execution.isBarId 0) (by simp only [c0] at hc; omega)
  obtain ⟨pc0, k0⟩ := ev
  cases k0 with
  | bar id c md =>
    simp only [Execution.isBarId, beq_iff_eq] at hb0
    subst hb0
    obtain ⟨-, hcn⟩ := bar0_sources (Q := Q) hp hX (g, j0) pc0 c ⟨md, hget0⟩ hg
      (by simp only; omega)
    subst hcn
    obtain ⟨rfl, -⟩ := bar_event_static hX (by omega) hget0
    have hf : X.IsBarrier (g, j0) 0 none pc0 := hget0
    obtain ⟨i0, pci, hgeti, hci⟩ := NamedBar.early_member_arrival (f := (g, j0)) hX
      (n := CtaBarrier.warps L.block) (by simp [CtaBarrier.warps, hbk]) rfl (Finset.card_range _)
      (fun w hw => by simp only [Finset.mem_range, CtaBarrier.warps, hbk] at hw ⊢; omega)
      (by decide) (bar0_sources (Q := Q) hp hX) hf (by simp only; omega)
      (by simp only; omega) (g := g / L.block * L.block) (by rw [hcta])
      (by simp only [Finset.mem_range, CtaBarrier.warps]; rw [hw0, hbk]; decide) (by
        rintro ⟨jx, pcx, hex⟩
        have h2 := bar0_exit (Q := Q) hp hX hex
        obtain ⟨i, -, ev', hget', hb', hc'⟩ := nth_of_count (X := X) (q := 0)
          (g := g / L.block * L.block) (k := jx) (P := Execution.isBarId 0)
          (by simp only [c0] at h2; omega)
        obtain ⟨pci, ki⟩ := ev'
        cases ki with
        | bar idi ci mi =>
          simp only [Execution.isBarId, beq_iff_eq] at hb'
          subst hb'
          have hci := (bar0_sources (Q := Q) hp hX _ _ _ ⟨mi, hget'⟩ hg0t (by simp only; omega)).2
          subst hci
          obtain ⟨rfl, -⟩ := bar_event_static hX (by omega) hget'
          exact ⟨i, pci, hget', by simp only; rw [hc', hc0]⟩
        | _ => simp [Execution.isBarId] at hb')
    simp only at hci
    rw [hc0] at hci
    -- the state of thread 0 at its first barrier-0 event: the first barrier, at position 2
    have hu0 : ∀ f, (⟨pci, .bar 0 none .sync⟩ : Event).kind ≠ .ub f := by simp
    have hli0 : i0 < (X.tr (g / L.block * L.block)).length :=
      (List.getElem?_eq_some_iff.mp hgeti).1
    rcases early (Q := Q) hp hX i0 (noUb_before hX hgeti) with h0 | ⟨h0, h2⟩ | ⟨σ, hσ, hP⟩
    · exfalso
      rcases Frame.fired (C := thread Q L) (fun g hg => thread_sound hp hg) hX hgeti with
        ⟨σ, o, hσ', -⟩ | ⟨-, pc', f, hf'⟩
      · rw [h0] at hσ'; cases hσ'
      · cases hf'
    · simp only [c0] at h2; omega
    have hcn : σ.2 (.bar 0) = c0 X (g / L.block * L.block) i0 := by
      rw [fcount hσ (.bar 0), cls_bar0]
    obtain ⟨x0, n0⟩ := σ
    simp only at hcn
    rcases x0 with s0 | y
    swap; · simp only [EarlyPos] at hP; simp only [c0] at hcn; omega
    have hev := start_ev hp hX hgeti hσ hu0
    obtain ⟨site, tm, xx, bw⟩ := s0
    have hbar0 : site = .bar0 := by
      cases site <;> simp only [EarlyPos] at hP <;> simp only [Startup.Ev] at hev
      all_goals first
        | rfl
        | (simp only [c0] at hcn; omega)
        | (simp at hev)
    subst hbar0
    -- the predecessor states: the allocation's store at position 1
    cases i0 with
    | zero =>
      exfalso
      rw [Frame.stateAt_zero] at hσ
      have h2 := congrArg Prod.fst (Option.some.inj (Option.some.inj hσ))
      change Code.enter (Startup.code Q L _) (Code.withStubs (frag Q L _) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L _)) (Startup.init L _) = _ at h2
      rw [enter_inl enterOf_init] at h2
      have h3 := Sum.inl.inj h2
      unfold Startup.init at h3
      rw [hw0] at h3
      simp only [show (0 : Nat) < 32 by decide, ↓reduceIte] at h3
      cases h3
    | succ i' =>
      obtain ⟨s', n', e', hσ', hget', hsu⟩ := prev_start (by omega) hσ
      obtain ⟨site', tm', x', bw'⟩ := s'
      have hl0 : laneOf L (g / L.block * L.block) = 0 := by
        unfold laneOf; rw [hw0]
      have hwr : site' = .allocWr := by
        cases site' <;> simp only [Startup.succ] at hsu
        all_goals first
          | rfl
          | (repeat' split at hsu
             all_goals simp_all [Startup.D.mk.injEq])
      subst hwr
      obtain ⟨rfl, -, -⟩ := allocWr_at (by omega) rfl hσ'
      have hu1 : ∀ f, e'.kind ≠ .ub f := fun f hf => by
        obtain ⟨pce, ke⟩ := e'
        simp only at hf
        subst hf
        have := ub_last hX hget' hgeti
        omega
      have hev' := start_ev hp hX hget' hσ' hu1
      simp only [Startup.Ev] at hev'
      obtain ⟨col, -, rfl⟩ := hev'
      have hc1 : c0 X (g / L.block * L.block) 1 ≤ 1 := by
        have := countP_mono_take (X := X) (g := g / L.block * L.block)
          (P := Execution.isBarId 0) (show 1 ≤ 1 + 1 by omega)
        simp only [c0] at hci ⊢
        omega
      obtain ⟨-, -, -, hbs⟩ := early_write (Q := Q) hp hX hget' hc1
      refine ⟨⟨11, ?_⟩, hci⟩
      rw [hget', hbs, hcta]
  | _ => simp [Execution.isBarId] at hb0

/-- **`BaseRead`**: the startup's load of the shared base returns the word 0. -/
theorem base_read (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    BaseRead Q L X := by
  intro g k pc s n a bs hσ hs he hloc hsz
  have hg := Frame.lt_of_get hX he
  have hbk : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  -- one barrier-0 event before the read
  have hc : c0 X g k = 1 := by
    rcases early (Q := Q) hp hX k (noUb_before hX he) with h0 | ⟨h0, -⟩ | ⟨σ, hσ', hP⟩
    · rw [hσ] at h0; cases h0
    · rw [hσ] at h0; cases h0
    · rw [hσ] at hσ'
      cases hσ'
      obtain ⟨site, tm, x, bw⟩ := s
      simp only at hs
      subst hs
      have := fcount hσ (.bar 0)
      rw [cls_bar0] at this
      simp only at this
      simp only [EarlyPos] at hP
      simp only [c0]
      omega
  have hc1 : c0 X g (k + 1) = 1 := by
    rw [c0_succ (show (X.tr g)[k]? = _ from he)]
    simp [hc, Execution.isBarId]
  obtain ⟨⟨pcw, hw⟩, hc2⟩ := writer hp hX hg hkl hc
  have hcta : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  have hg0t : g / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hsame0 : SameCta L (g / L.block * L.block) g := ⟨hg0t, hg, hcta⟩
  refine read_of_last_write hX (e := .thread (g, k)) (w := .thread (g / L.block * L.block, 1))
    (Or.inl ⟨pc, he⟩) (Or.inl ⟨pcw, hw⟩) (by rw [hloc]) hsz.symm (by rw [hsz]; rfl)
    (fun _ _ => .inl (bar0_before (Q := Q) hp hX hsame0 hkl (by rw [hc2, hc]; omega)
      (by rw [hc2]; omega))) ?_
  intro k' hk' w' dst' bytes hm hcov
  have hcov' := hcov
  obtain ⟨hsp, hct, -⟩ := hcov'
  rw [hloc] at hsp hct
  simp only [Loc.at] at hsp hct
  rcases w' with ⟨h, j⟩ | ⟨⟨h, j⟩, p⟩
  · obtain ⟨⟨pcx, hgx⟩, hcta'⟩ := thread_write_cta hp hX hm
    have hhc : h / L.block = g / L.block := by rw [← hcta' hsp.symm, ← hct]
    have hh := Frame.lt_of_get hX hgx
    have hjl : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hgx).1
    by_cases hj : c0 X h j ≤ 1
    · obtain ⟨rfl, hh0, -, -⟩ := early_write (Q := Q) hp hX hgx hj
      left
      have : h = g / L.block * L.block := by
        rw [← hhc]
        have := Nat.div_add_mod h L.block
        rw [Nat.mul_comm] at this
        omega
      rw [this]
    · right; right
      exact .inl (bar0_before (Q := Q) hp hX ⟨hg, hh, hhc.symm⟩ hjl (by rw [hc1]; omega)
        (by rw [hc1]))
  · obtain ⟨e', hge', hwo, hnt⟩ := memWrites_async_issuer hm
    obtain ⟨pce, a', sp, rfl, x, y, z, hwl⟩ := async_copy hX hge' hwo hnt
    have hlc := copy_cta hp hX hge' hwl
    obtain ⟨f, jf, pcf, hfc, hft, hfget, hfb⟩ := issue_fence hp hX hge'
    have hh := Frame.lt_of_get hX hge'
    have hfl : jf < (X.tr f).length := (List.getElem?_eq_some_iff.mp hfget).1
    have hf2 := fence_c0 (Q := Q) hp hX hfget
    right; right
    have hgh : g / L.block = h / L.block := hct.trans hlc
    refine ⟨⟨dst', true, hm.intent, hcov⟩, .inl ⟨(f, jf), some (.shared .cta), none,
      ⟨pcf, hfget⟩, hft, ⟨?_, ?_⟩, ⟨hft, hh, by rw [hfc]⟩, ?_, hfb⟩⟩
    · simp [Loc.at, hloc]
    · simp only [Loc.at, hloc]
      rw [hfc, ← hgh]
    · exact bar0_before (Q := Q) hp hX ⟨hg, hft, by rw [hfc, ← hgh]⟩ hfl (by rw [hc1]; omega)
        (by rw [hc1])

/-- **Every launched thread is followed with `Ref`**, with no premise: `good_all` with
`base_read`. -/
theorem good_all' (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (k : Nat) :
    Frame.FollowedAt (thread Q L) (fun g => Ref Q L g) X g k :=
  good_all hp hX (base_read hp hX) hg k

end
end PTX.Kernels.InklingRelDecode.Proof2
