-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk4Class
public import Kernels.InklingRelDecode.Proof.Interface.IpTmZero
public import Kernels.InklingRelDecode.Proof.Interface.Reach

@[expose] public section

/-!
# Warp lockstep: the static operands of the warp-collective `tcgen05` events

The lanes of a warp that make their `n`-th warp-collective `tcgen05` event must use the same
operands (`tcStatic`: the event without the values it loaded or stored). `tcStat L g s` is the
static part of the event of the state `s` of thread `g`, read off the state's own fields:

* the allocation: the word at the shared base of the thread's CTA, 512 columns; the permit
  relinquishment; the deallocation: the epilogue's base `d.pr.tm`, 512 columns;
* the softmax region's loads and stores: the Tensor Memory address of the S and P tile
  (`Sm.tileAddr`: the stage `d.i % 2`, the base `d.e.tm`, the recorded lane bits) or of the `O`
  tile (`Sm.oAddr`: the base and the recorded lane bits), with the shape of the instruction; the
  lane bits are the warp index after tracking (`BwW`, `sm_bw`);
* the epilogue's load: `d.pr.taddr` (the lane bits the broadcast returned, which are the warp
  index after tracking (`BwW`, `epi_bw`), and the column base `d.pr.c0`);
* the waits.

`tcStat_event`: the event of a warp-collective `tcgen05` state has `tcStat` as its `tcStatic`
(from the shapes of the sites). `tcStat_lane`: two lanes of a warp at synchronizing states of one
key have one `tcStat`, given that the Tensor Memory base word of every default-partition state is 0
(`TmZ`, `Interface.tmz_inv`) and the meaning of the states (`TReach`): the stage `d.i` is in the
key, the warp's lanes are the warp's, and the base is 0.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (dTc smKey dSy smSy epSy dsSy ds_site_eq
  sm_key_comps ep_site_eq d_pc_range rangeOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The static part of the event of a warp-collective `tcgen05` state.** -/
def tcStat (L : Launch) (g : Nat) : TSt → TcKind
  | .d (.dstart d) =>
    match d.site with
    | .alloc => .resource .one (some ⟨.shared, g / L.block, L.sharedBase⟩) (.alloc 512)
    | _ => .resource .one none .relinquish
  | .d (.sm d) =>
    match d.site with
    | .ldS => .ld (Sm.tileAddr L g d) [] (.s16x32bx2 64)
    | .tmemSt => .st (Sm.tileAddr L g d) [] (.s16x32bx2 32)
    | .ldO => .ld (Sm.oAddr L g d) [] (.s16x32bx2 64)
    | .stO => .st (Sm.oAddr L g d) [] (.s16x32bx2 64)
    | .waitLd | .waitLdO => .waitLd
    | _ => .waitSt
  | .d (.epi d) =>
    match d.site with
    | .ld => .ld d.pr.taddr [] (.s16x32bx2 64)
    | .waitLd => .waitLd
    | _ => .resource .one none (.dealloc d.pr.tm 512)
  | _ => .waitLd

/-- **The event of a warp-collective `tcgen05` state has the static part of its state.** -/
theorem tcStat_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) (hs : tcSt s = true) :
    ∃ pc kd, e = ⟨pc, .tc kd⟩ ∧ tcStatic kd = tcStat L g s := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (tc_not_exit hs)
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hb2 : L.block = 256 := hpre.block
  have hSh := ProA.sharedOk_of_pre hpre
  cases s with
  | w s => simp [tcSt] at hs
  | d s =>
    cases s with
    | pro d => simp [tcSt, dTc] at hs
    | dstart d =>
      have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
      obtain ⟨site, tm⟩ := d
      simp only [tcSt, dTc, decide_eq_true_eq] at hs
      rcases hs with rfl | rfl
      · simp only [DStart.Shape] at hshape
        exact ⟨_, _, hshape, rfl⟩
      · simp only [DStart.Shape] at hshape
        exact ⟨_, _, hshape, rfl⟩
    | sm d =>
      have hshape := Sm.shape hb2 hSh (fired_sm hF)
      have hshapeO := Sm.shapeO (fired_sm hF)
      have hw := fun h => Sm.shape_waitLdO hb (fired_sm hF) h
      simp only [tcSt, dTc, decide_eq_true_eq] at hs
      unfold Sm.Shape at hshape
      unfold Sm.ShapeO at hshapeO
      obtain ⟨site, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
      simp only at hs hshape hshapeO
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at hshape hshapeO
      · obtain ⟨vals, -, he'⟩ := hshape; exact ⟨_, _, he', rfl⟩
      · exact ⟨_, _, hshape, rfl⟩
      · obtain ⟨vals, -, -, -, he'⟩ := hshape; exact ⟨_, _, he', rfl⟩
      · exact ⟨_, _, hshape, rfl⟩
      · obtain ⟨vals, -, he'⟩ := hshapeO; exact ⟨_, _, he', rfl⟩
      · exact ⟨_, _, hw rfl, rfl⟩
      · obtain ⟨vals, -, -, -, he'⟩ := hshapeO; exact ⟨_, _, he', rfl⟩
      · exact ⟨_, _, hshape, rfl⟩
    | epi d =>
      have hshape := Epi.shape hb (fired_epi hF)
      simp only [tcSt, dTc, decide_eq_true_eq] at hs
      unfold Epi.Shape at hshape
      obtain ⟨site, pr, o, sk⟩ := d
      simp only at hs hshape
      rcases hs with rfl | rfl | rfl <;> simp only at hshape
      · obtain ⟨vals, -, he'⟩ := hshape; exact ⟨_, _, he', rfl⟩
      · exact ⟨_, _, hshape, rfl⟩
      · exact ⟨_, _, hshape, rfl⟩

/-- The lane bits an epilogue state recorded from its broadcast are its warp index at the load
(`epi_bw`, after tracking); those a softmax state recorded are the thread's warp index from the
S load to the end of the iteration (`sm_bw`). -/
def BwW (L : Launch) (g : Nat) : TSt → Prop
  | .d (.epi d) => d.site = .ld → d.pr.bw = d.pr.w
  | .d (.sm d) => Sm.BwSite d.site → d.stg.bw = g % L.block / 32
  | _ => True

/-- **Two lanes of a warp at warp-collective `tcgen05` states of one key have one static part.** -/
theorem tcStat_lane {g h : Nat} (hw : SameWarp L g h) {s s' : TSt} (hs : tcSt s = true)
    (hs' : tcSt s' = true) (hk : (kernelSkel Q L).key g s = (kernelSkel Q L).key h s')
    (hz : TmZ s) (hz' : TmZ s') (hm : TReach Q L g s) (hm' : TReach Q L h s')
    (hb : BwW L g s) (hb' : BwW L h s') :
    tcStat L g s = tcStat L h s' := by
  have hsy := tcSt_sy hs
  have hsy' := tcSt_sy hs'
  have hpc : TSt.pc s = TSt.pc s' := by
    have h1 := (kernelSkel Q L).pc_key (g := g) hsy
    have h2 := (kernelSkel Q L).pc_key (g := h) hsy'
    rw [← h1, ← h2, hk]
  have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
  have hc : g / L.block = h / L.block := hw.1.2.2
  cases s with
  | w s => simp [tcSt] at hs
  | d a =>
    cases s' with
    | w s => simp [tcSt] at hs'
    | d b =>
      have hda : dSy a = true := hsy
      have hdb : dSy b = true := hsy'
      have r1 := d_pc_range hda
      have r2 := d_pc_range hdb
      have hpc' : DComp.pc a = DComp.pc b := hpc
      cases a <;> cases b <;> first
        | (exfalso; simp only [rangeOf, DComp.pc] at r1 r2 hpc'; omega)
        | skip
      · -- the common start
        rename_i d d'
        obtain ⟨site, tm⟩ := d
        obtain ⟨site', tm'⟩ := d'
        simp only [dSy, Bool.and_eq_true] at hda hdb
        have hsite := ds_site_eq hda.1 hdb.1 hpc'
        simp only at hsite
        subst hsite
        simp only [tcSt, dTc, decide_eq_true_eq] at hs
        rcases hs with rfl | rfl <;> simp [tcStat, hc]
      · exact absurd hs (by simp [tcSt, dTc])
      · -- the softmax region
        rename_i d d'
        have hk' : smKey L g d = smKey L h d' := hk
        obtain ⟨hsite, -, hi, -⟩ := sm_key_comps hda hdb hk'
        have hz1 : d.e.tm = 0 := hz
        have hz2 : d'.e.tm = 0 := hz'
        have hb1 : Sm.BwSite d.site → d.stg.bw = g % L.block / 32 := hb
        have hb2 : Sm.BwSite d'.site → d'.stg.bw = h % L.block / 32 := hb'
        obtain ⟨site, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
        obtain ⟨site', e0', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
        simp only at hsite hi hz1 hz2 hb1 hb2
        subst hsite hi
        simp only [tcSt, dTc, decide_eq_true_eq] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (have e1 := hb1 trivial
           have e2 := hb2 trivial
           simp [tcStat, Sm.tileAddr, Sm.oAddr, Sm.r45, hz1, hz2, hw2, e1, e2])
      · -- the epilogue
        rename_i d d'
        have hsite := ep_site_eq hda hdb hpc'
        have hz1 : d.pr.tm = 0 := hz
        have hz2 : d'.pr.tm = 0 := hz'
        have m1 : Epi.Means Q L g d.pr := hm.2
        have m2 : Epi.Means Q L h d'.pr := hm'.2
        have hb1 : d.site = .ld → d.pr.bw = d.pr.w := hb
        have hb2 : d'.site = .ld → d'.pr.bw = d'.pr.w := hb'
        obtain ⟨site, pr, o, sk⟩ := d
        obtain ⟨site', pr', o', sk'⟩ := d'
        simp only at hsite hz1 hz2 m1 m2 hb1 hb2
        subst hsite
        simp only [tcSt, dTc, decide_eq_true_eq] at hs
        have hwp : pr.w = pr'.w := by rw [m1.w, m2.w, hw2]
        have hc0 : pr.c0 = pr'.c0 := by rw [m1.c0, m2.c0, hz1, hz2]
        rcases hs with rfl | rfl | rfl
        · have hbw : pr.bw = pr'.bw := by rw [hb1 rfl, hb2 rfl, hwp]
          simp [tcStat, Epi.Prm.taddr, hbw, hc0]
        all_goals simp [tcStat, hz1, hz2]

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
