-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.BaseWRead
public import Kernels.InklingRelDecode.Proof2.Lib.CopyCta
public import Kernels.InklingRelDecode.Proof.Interface.BaseWPhase
public import Kernels.InklingRelDecode.Proof.Interface.ScFence

@[expose] public section

/-!
# Every tensor copy is after every read of the base word, under the tracking up to the stops

`copy_w` is the field `copy` of `BaseSources` (`BaseWRead.lean`): `base_before_copy`
(`ScFence.lean`) with `WeakTracked` in place of `Frame.Tracked`, `Bar1Exits` and `RoleReads`.

* The copy writes its issuer's CTA (`copyW_cta`: `fires_copy_base` at the issue, followed or not),
  so the issuer is a thread of the read's CTA.
* If the machine follows the issuer at the issue, the issue is the prologue's (after the issuer's
  `fnc0`) or the loader's (after a barrier-1 event, `one_le_b1N_loader`). If it does not, the
  issuer stopped earlier: at the prologue's `bar18`, which is after its `fnc0`, or at the
  dispatch, which is after a barrier-1 event (`one_le_b1N_ldRole`).
* After `fnc0` of the issuer: the fence is after the read (two barrier-0 events before it,
  `base_read_before_count`) and before the issue in program order.
* After a barrier-1 event: the issuer's arrival of ordinal 0 synchronizes with the arrival of
  ordinal 0 of the CTA's thread 0 (`Bar.bar1_member`), which is thread 0's `bar18`, after its
  `fnc1`. The exit premise of `Bar.bar1_member` holds because thread 0 exits only from the
  epilogue, or after its stop at `bar18`, and both are after its arrival of ordinal 0
  (`exitW_arrival0`). Thread 0 is followed up to that arrival: a stop before it would be an earlier
  barrier-1 event (`arrivalW0_state`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Bar PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem b1N_monoW {g j k : Nat} (h : j ≤ k) : b1N X g j ≤ b1N X g k :=
  (List.take_sublist_take_left h).countP_le

/-- **A tensor copy writes its issuer's CTA**, at any issue event, followed or not. -/
theorem copyW_cta (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k pc a : Nat}
    {sp : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) {x y z : Nat}
    {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites (.async (g, k) (.write (.load x y z))) dst bs) :
    dst.loc.cta = g / L.block := by
  obtain ⟨o, addr, b, -, ⟨pc', hget'⟩, hloc, -⟩ := hw
  rw [he] at hget'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hget'
  obtain ⟨-, -, hsp⟩ := hget'
  have hbase : sp.sharedBase.cta = g / L.block := by
    rcases Frame.fired hS hX he with ⟨σ, o', -, hF⟩ | ⟨-, pc'', f, h⟩
    · rcases Code.fired_op hF with ⟨pc'', f, h⟩ | ⟨t, ins, hc, hf⟩
      · cases h
      · have hop : tensorOp ins.op = true := by
          cases hq : tensorOp ins.op
          · exact (fires_notTensor (eventTmpl_notTensor hq) hf a sp rfl).elim
          · rfl
        have hl : localCopyOp ins.op = true := by
          cases hl : localCopyOp ins.op
          · have := OpPcsFast.mem kernel_copy_local hc (by simp [hop, hl])
            simp at this
          · rfl
        exact fires_copy_base hl hf rfl
    · cases h
  simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hloc
  obtain ⟨slot, -, hl⟩ := hloc
  rw [← hl]
  rw [hsp] at hbase
  exact hbase

/-- **A tensor copy issued at a followed state** is the prologue's, after `fnc0`, or the
loader's. -/
theorem copyW_cls (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k pc a : Nat} {sp : TensorCopy.Spec}
    {s : TSt} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hσ : St Q L X g k = some (some s)) :
    (∃ d : ProA.D, s = .d (.pro d) ∧ ProA.Site.fnc0.pc < d.site.pc) ∨
      ∃ d P, s = .w (.loader d P) := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : tensorOp ins.op = true := by
    cases hq : tensorOp ins.op
    · exact (fires_notTensor (eventTmpl_notTensor hq) hf a sp rfl).elim
    · rfl
  have hpw : TSt.pc s ∈ copyPcs := OpPcsFast.mem kernel_copy_pcs hc hop
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (by exact worker_pc_notCopy w.site)
    | idle d => exact absurd hpw (idle_pc_notCopy d.site)
    | mma d _ => exact absurd hpw (mma_pc_notCopy d.site)
    | exit x => exact absurd hpw (exit_pc_notCopy x.site)
    | loader d P => exact .inr ⟨d, P, rfl⟩
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (dstart_pc_notCopy d.site)
    | sm d => exact absurd hpw (sm_pc_notCopy d.site)
    | epi d => exact absurd hpw (epi_pc_notCopy d.site)
    | pro d =>
      obtain ⟨i, hi, hs⟩ := ptc_index _ (pro_pc_copy d.site hpw)
      exact .inl ⟨d, rfl, by rw [hs]; exact ptc_pc_gt i hi⟩

/-- **A base-word stop of a default-partition thread is a barrier-1 event.** -/
theorem stopW_b1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g j : Nat} {s : TSt}
    (hd : g % L.block < 128) (hj : j < (X.tr g).length) (hσ : St Q L X g j = some (some s))
    (hb : BaseStop s) : 1 ≤ b1N X g (j + 1) := by
  obtain ⟨dd, rfl, -⟩ := dphase_inv hpre hX hS hd j s hj.le hσ
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[j]? = some e := ⟨_, List.getElem?_eq_getElem hj⟩
  have hget : X.get (g, j) = some e := he
  have h1 := event_b1 hpre hX hS hget hσ
  have hB : tB1 (.d dd) = true := by
    cases dd with
    | pro d =>
      obtain ⟨site, dt⟩ := d
      obtain ⟨hs, -⟩ := hb
      simp only at hs
      subst hs
      rfl
    | _ => exact hb.elim
  unfold b1N
  rw [countP_take_succ _ he, h1, hB]
  simp

/-- **A default-partition thread that exits has made its barrier-1 arrival of ordinal 0**: it
exits from the epilogue, or after its stop at `bar18`. -/
theorem exitW_arrival0 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hW : WeakTracked Q L X) {g j pcx : Nat}
    (hd : g % L.block < 128) (he : X.get (g, j) = some ⟨pcx, .exit⟩) :
    ∃ i pc', X.IsBarrier (g, i) 1 none pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId 1) = 0 := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have h1 : ∃ k, k ≤ (X.tr g).length ∧ 1 ≤ b1N X g k := by
    by_cases hTT : TT Q L X (g, j)
    · obtain ⟨s, hσ⟩ := event_state_at hS hX he (by intro pc f h; cases h) hTT
      obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
      have hop : isExitOp ins.op = true := by
        rcases fires_exit_op hf (rfl : (⟨pcx, .exit⟩ : Event).kind = .exit) with h | h <;>
          simp [isExitOp, h]
      have hpw : TSt.pc s ∈ exitPcs := OpPcsFast.mem kernel_exit_pcs hc hop
      obtain ⟨dd, rfl, hb1⟩ := dphase_inv hpre hX hS hd j s hj.le hσ
      refine ⟨j, hj.le, ?_⟩
      rw [hb1]
      cases dd with
      | dstart d => exact absurd hpw (fun h => by simpa using dstart_exit_pc d.site h)
      | pro d => exact absurd hpw (fun h => by simpa using pro_exit_pc d.site h)
      | sm d => simp only [dPh]; split <;> simp
      | epi d => simp only [dPh]; split <;> simp
    · obtain ⟨jj, hjj, s, hσ, hb⟩ := hW g (j + 1) hg (not_not.mp hTT)
      exact ⟨jj + 1, by omega, stopW_b1 hpre hX hS hd (by omega) hσ hb⟩
  obtain ⟨k, hk, hk1⟩ := h1
  obtain ⟨i, pc', -, hi, hc⟩ := arrival1_before hpre hX (h := g) (k := k) (r := 0) hk1
  exact ⟨i, pc', hi, hc⟩

/-- **A default-partition thread is followed up to its barrier-1 arrival of ordinal 0**: a stop
before it would be an earlier barrier-1 event. -/
theorem arrivalW0_state (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hW : WeakTracked Q L X) {g i pc : Nat}
    (hd : g % L.block < 128) (hf : X.IsBarrier (g, i) 1 none pc)
    (hc : ((X.tr g).take i).countP (Execution.isBarId 1) = 0) :
    ∃ s, St Q L X g i = some (some s) := by
  have hg : g < L.threads := Frame.lt_of_get hX hf
  have he : X.get (g, i) = some ⟨pc, .bar 1 none .sync⟩ := hf
  have hli : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  refine state_of_prev hS hX he bar_not_ub ?_
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · exact .inl h0
  · refine .inr ⟨i - 1, by omega, ?_⟩
    show St Q L X g (i - 1 + 1) ≠ some none
    intro hn
    rw [show i - 1 + 1 = i by omega] at hn
    obtain ⟨jj, hjj, s, hσ, hb⟩ := hW g i hg hn
    have h1 := stopW_b1 hpre hX hS hd (by omega) hσ hb
    have h2 : b1N X g (jj + 1) ≤ b1N X g i := b1N_monoW (by omega)
    have h3 : b1N X g i = 0 := hc
    omega

/-- **`ProxyBefore` for every tensor copy that writes the read's CTA**, under the tracking up to
the base-word stops: the field `copy` of `BaseSources`. -/
theorem copy_w (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hW : WeakTracked Q L X) :
    ∀ {h kr : Nat}, kr < (X.tr h).length → BaseReadAt Q L X h kr →
    ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → h < L.threads →
    ∀ {l : Loc}, l.space = .shared → l.cta = h / L.block →
      (∃ x y z dst bs, X.MemWrites (.async i (.write (.load x y z))) dst bs ∧ dst.Covers l) →
      ProxyBefore L X (h, kr) i l := by
  intro h kr hr hb i pc a sp he hh l hls hlc hwr
  obtain ⟨g, k⟩ := i
  have hE := earlyTT_of_weak hX hS hW
  have hbk : L.block = 256 := hpre.block
  have hblk : 0 < L.block := by omega
  have hgi : g < L.threads := Frame.lt_of_get hX he
  have hli : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hcta : g / L.block = h / L.block := by
    obtain ⟨x, y, z, dst, bs, hw, hcov⟩ := hwr
    have h1 : dst.loc.cta = g / L.block := copyW_cta hX hS he hw
    rw [← h1, ← hlc]
    exact hcov.2.1.symm
  have hsame : SameCta L h g := ⟨hh, hgi, hcta.symm⟩
  -- the issue's state, or the issuer's stop before the issue
  have hcls : (∃ j ≤ k, ∃ d : ProA.D, St Q L X g j = some (some (.d (.pro d))) ∧
      ProA.Site.fnc0.pc < d.site.pc) ∨ 1 ≤ b1N X g k := by
    by_cases hTT : TT Q L X (g, k)
    · obtain ⟨s, hσ⟩ := event_state_at hS hX he (by intro pc f h; cases h) hTT
      rcases copyW_cls hX hS he hσ with ⟨d, rfl, hd⟩ | ⟨d, P, rfl⟩
      · exact .inl ⟨k, le_rfl, d, hσ, hd⟩
      · exact .inr (one_le_b1N_loader hpre hX hS hli.le hσ)
    · obtain ⟨jj, hjj, s, hσ, hst⟩ := hW g (k + 1) hgi (not_not.mp hTT)
      cases s with
      | d s =>
        cases s with
        | pro d => exact .inl ⟨jj, by omega, d, hσ, by rw [hst.1]; decide⟩
        | _ => exact hst.elim
      | w s =>
        cases s with
        | worker w =>
          obtain ⟨site, P⟩ := w
          obtain ⟨hs, -⟩ := hst
          simp only at hs
          subst hs
          have hjl : jj ≤ (X.tr g).length := by omega
          exact .inr (le_trans (one_le_b1N_ldRole hpre hX hS hjl hσ) (b1N_monoW (by omega)))
        | _ => exact hst.elim
  rcases hcls with ⟨j, hj, d, hσ, hpast⟩ | hb1
  · -- after the issuer's own `fnc0`
    have hcover : AsyncFenceCovers L (some (.shared .cta)) g l := ⟨hls, by rw [hlc, hcta]⟩
    obtain ⟨j0, hj0, d0, hσ0, hs0⟩ := exists_pastPro (X := X)
      (fun h' a b => ProA.next_cross_fnc0 h' a b) (by decide) (by decide) j _ hσ
      (show PastPro ProA.Site.fnc0 (.d (.pro d)) from hpast)
    have hj0' : j0 < (X.tr g).length := by omega
    obtain ⟨e0, he0⟩ : ∃ e0, X.get (g, j0) = some e0 :=
      ⟨_, List.getElem?_eq_getElem hj0'⟩
    obtain ⟨pcf, hev⟩ := fnc_event hX hS hT hgi he0 hσ0 (Or.inl hs0)
    have hfence : X.IsProxyFence (g, j0) (.async (some (.shared .cta))) none :=
      ⟨pcf, by rw [he0, hev]⟩
    refine ⟨(g, j0), _, _, hfence, hgi, hcover, ⟨hgi, hgi, rfl⟩, ?_, ?_⟩
    · exact base_read_before_count hpre hX hS hE hsame hr hb
        (bar0_ordinal_two hX hS hj0'.le hσ0 (by simp [tLb_pro])) hj0'
    · exact .single (.inl (po_of_source_not_access (X := X) (e := (g, j0)) (f := (g, k)) rfl
        (show j0 < k by omega) hli (by rw [he0, hev]; rfl)))
  · -- after the issuer's barrier-1 arrival of ordinal 0, which follows thread 0's `fnc1`
    obtain ⟨j0, pcf, hj0, hf0, hc0⟩ := arrival1_before hpre hX (h := g) (k := k) (r := 0)
      (by omega)
    have hp : j0 + 1 < (X.tr g).length := by omega
    have hg0 : g / L.block * L.block < L.threads :=
      lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hgi
    have hd0 : g / L.block * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
    have hcta0 : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hblk
    obtain ⟨i0, pc0, hf00, hc00⟩ := Bar.bar1_member hpre hX (f := (g, j0)) hf0 hp
      (g := g / L.block * L.block) hcta0 (fun ⟨jx, pcx, hex⟩ => by
        obtain ⟨i', pc', hi', hc'⟩ := exitW_arrival0 hpre hX hS hW hd0 hex
        exact ⟨i', pc', hi', hc'.trans hc0.symm⟩)
    have hc00' : ((X.tr (g / L.block * L.block)).take i0).countP (Execution.isBarId 1) = 0 :=
      hc00.trans hc0
    have he00 : X.get (g / L.block * L.block, i0) = some ⟨pc0, .bar 1 none .sync⟩ := hf00
    have hli0 : i0 < (X.tr (g / L.block * L.block)).length :=
      (List.getElem?_eq_some_iff.mp he00).1
    obtain ⟨s0, hσ0⟩ := arrivalW0_state hpre hX hS hW hd0 hf00 hc00'
    obtain ⟨dd, rfl, hb1'⟩ := dphase_inv hpre hX hS hd0 i0 s0 hli0.le hσ0
    have hbar := event_b1 hpre hX hS he00 hσ0
    rw [isBarId_bar] at hbar
    have h0 : (dPh dd).2 = 0 := by rw [← hb1']; exact hc00'
    obtain ⟨dd', rfl, hs⟩ := dB1_phase0 h0 hbar.symm
    obtain ⟨j1, hj1, d1, hσ1, hs1⟩ := exists_pastPro (X := X)
      (fun h' a b => ProA.next_cross_fnc1 h' a b) (by decide) (by decide) i0 _ hσ0
      (by show ProA.Site.fnc1.pc < dd'.site.pc; rw [hs]; decide)
    have hj1' : j1 < (X.tr (g / L.block * L.block)).length := by omega
    obtain ⟨e1, he1⟩ : ∃ e1, X.get (g / L.block * L.block, j1) = some e1 :=
      ⟨_, List.getElem?_eq_getElem hj1'⟩
    obtain ⟨pcf1, hev⟩ := fnc_event hX hS hT hg0 he1 hσ1 (Or.inr hs1)
    have hfence : X.IsProxyFence (g / L.block * L.block, j1) (.async (some (.shared .cta)))
        none := ⟨pcf1, by rw [he1, hev]⟩
    have hsame0 : SameCta L h (g / L.block * L.block) :=
      ⟨hh, hg0, by rw [hcta0]; exact hcta.symm⟩
    have hcover0 : AsyncFenceCovers L (some (.shared .cta)) (g / L.block * L.block) l :=
      ⟨hls, by rw [hlc, hcta0, hcta]⟩
    refine ⟨(g / L.block * L.block, j1), _, _, hfence, hg0, hcover0,
      ⟨hg0, hgi, by rw [hcta0]⟩, ?_, ?_⟩
    · exact base_read_before_count hpre hX hS hE hsame0 hr hb
        (bar0_ordinal_two hX hS hj1'.le hσ1 (by simp [tLb_pro])) hj1'
    · exact Bar.bar1_baseCausality hpre hX ⟨hg0, hgi, hcta0⟩ hf00 hf0 hp hc00 hj1 hj0 hli

-- `copy_w` has the form of the field `copy` of `BaseSources`.
example (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hW : WeakTracked Q L X)
    (hz : AllocWordZero Q L X) : BaseSources Q L X :=
  ⟨hz, copy_w hpre hX hS hT hW⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
