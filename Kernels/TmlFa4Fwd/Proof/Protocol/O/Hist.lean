-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Top.JRStub
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Post
public import Kernels.TmlFa4Fwd.Proof.Protocol.O.Obj
public import Lemmas.Protocol.MbarOneShot
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Win
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The final O barriers are one-shot objects

A final O barrier of stage `st` is named only by the MMA warp's commit at `cm (10 + st)` and the
correction lanes' parity-0 polls (`o_use`). Two such commits of one CTA are one event: their lanes
are one (`win_lane`), and after the lane's commit no other one follows (`post_states`):
`commit_same`. So the object's history is its initialization with count 1, the one commit's
notification and polls of parity 0 (`o_hist`), and a successful poll observes the notification
(`MbarOneShot.Hist.observes_arrive`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem postSite_cm (st : Fin 2) : postSite st (.cm ⟨10 + st.val, by omega⟩) = false := by
  fin_cases st <;> rfl

theorem initOff_o : ∀ q : Fin 34, ∀ st : Fin 2, initOff q = oOff st →
    q.val = 18 + st.val ∧ initCnt q = 1 := by decide

theorem target_rank {s : TcCommit.Spec} {r r' : Fin 16} {l : Loc}
    (h : TcCommit.target s r = some l) (h' : TcCommit.target s r' = some l) : r = r' := by
  unfold TcCommit.target at h h'
  split_ifs at h h'
  simp only [Option.some.injEq] at h h'
  rw [← h'] at h
  simp only [Loc.mk.injEq] at h
  exact Fin.ext (by omega)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

/-- An event naming a final O barrier, from its followed state. -/
theorem o_event {st : Fin 2} {h k : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hm : MbarOf e (obj L g (oOff st))) (hni : ∀ c, e.kind ≠ .mbInit (obj L g (oOff st)) c) :
    ∃ σ, Frame.stateAt (thread p L) X h k = some (some σ) ∧ JR p L h σ ∧
      h / L.block = g / L.block ∧
      ((∃ d n s, σ = (.inr ⟨.mma, .inr ⟨(), d⟩⟩, n) ∧ (∃ c : Fin 12, c.val = 10 + st.val ∧
          d.site = .cm c) ∧ e.kind = .tc (.commit s)) ∨
        ∃ d n ok, σ = (.inr ⟨.correction, d⟩, n) ∧ d.site = .fw st 0 ∧
          e.kind = .wait (obj L g (oOff st)) 0 ok true .cta) := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kind⟩ := e
    rintro f rfl
    simp only [MbarOf] at hm
  obtain ⟨σ, hσ, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) he hub
  obtain ⟨hc, h2⟩ := o_use hp hX he hσ hJ hi hev hm hni
  exact ⟨σ, hσ, hJ, hc, h2⟩

set_option maxHeartbeats 4000000 in
/-- **Two stage-`st` commits of one CTA are one event.** -/
theorem commit_same {st : Fin 2} {z jc h k pc pc' : Nat} {s s' : TcCommit.Spec}
    {rank rank' : Fin 16}
    (hc : X.get (z, jc) = some ⟨pc, .tc (.commit s)⟩)
    (ht : TcCommit.target s rank = some (obj L z (oOff st)))
    (hc' : X.get (h, k) = some ⟨pc', .tc (.commit s')⟩)
    (ht' : TcCommit.target s' rank' = some (obj L z (oOff st))) : (h, k) = (z, jc) := by
  obtain ⟨σ, hσ, hJ, -, hc1⟩ := o_event hp hX hFw (g := z) hc ⟨rank, ht⟩
    (by intro c h; cases h)
  obtain ⟨σ', hσ', hJ', hcta, hc2⟩ := o_event hp hX hFw (g := z) hc' ⟨rank', ht'⟩
    (by intro c h; cases h)
  rcases hc1 with ⟨d, n, sp, rfl, ⟨c, hcv, hs⟩, -⟩ | ⟨d, n, ok, rfl, -, hk⟩
  swap; · cases hk
  rcases hc2 with ⟨d', n', sp', rfl, ⟨c', hcv', hs'⟩, -⟩ | ⟨d', n', ok, rfl, -, hk⟩
  swap; · cases hk
  have hz := Frame.lt_of_get hX hc
  have hh := Frame.lt_of_get hX hc'
  have h12 := jr_mma hJ
  have h12' := jr_mma hJ'
  have hw : SameWarp L z h := ⟨⟨hz, hh, hcta.symm⟩, by
    have : z % L.block / 32 = 12 := h12
    have : h % L.block / 32 = 12 := h12'
    omega⟩
  have hzh := win_lane hX hw hσ hσ' (by rw [hs]; rfl) (by rw [hs']; rfl)
  subst hzh
  have hcc : c = ⟨10 + st.val, by omega⟩ := Fin.ext hcv
  have hcc' : c' = ⟨10 + st.val, by omega⟩ := Fin.ext hcv'
  rw [hcc] at hs
  rw [hcc'] at hs'
  rcases Nat.lt_trichotomy jc k with hlt | heq | hgt
  · exfalso
    have hkl : k ≤ (X.tr z).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr z)[k]? = _ from hc')).1.le
    obtain ⟨d2, n2, h2, hp2⟩ := post_states hσ hs k hlt hkl _ hσ'
    simp only [Mma.minj, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at h2
    obtain ⟨rfl, -⟩ := h2
    rw [hs', postSite_cm] at hp2
    cases hp2
  · rw [heq]
  · exfalso
    have hjl : jc ≤ (X.tr z).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr z)[jc]? = _ from hc)).1.le
    obtain ⟨d2, n2, h2, hp2⟩ := post_states hσ' hs' jc hgt hjl _ hσ
    simp only [Mma.minj, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at h2
    obtain ⟨rfl, -⟩ := h2
    rw [hs, postSite_cm] at hp2
    cases hp2

set_option maxHeartbeats 8000000 in
/-- **The final O barrier of stage `st` is a one-shot object** with the commit's notification as
its one arrival. -/
theorem o_hist {st : Fin 2} {z jc pc : Nat} {s : TcCommit.Spec} {rank : Fin 16}
    (hc : X.get (z, jc) = some ⟨pc, .tc (.commit s)⟩)
    (ht : TcCommit.target s rank = some (obj L z (oOff st))) :
    MbarOneShot.Hist X (obj L z (oOff st)) [(.async (z, jc) (.tcNotify rank), 0)] [] := by
  have mism : ∀ {h k : Nat} {e : Event}, X.get (h, k) = some e →
      MbarOf e (obj L z (oOff st)) → (∀ c, e.kind ≠ .mbInit (obj L z (oOff st)) c) →
      (∃ sp, e.kind = .tc (.commit sp)) ∨
        (∃ ok, e.kind = .wait (obj L z (oOff st)) 0 ok true .cta) := by
    intro h k e he hm hni
    obtain ⟨σ, -, -, -, h2⟩ := o_event hp hX hFw he hm hni
    rcases h2 with ⟨d, n, sp, -, -, hk⟩ | ⟨d, n, ok, -, -, hk⟩
    · exact .inl ⟨sp, hk⟩
    · exact .inr ⟨ok, hk⟩
  have hq := obj_initFirst hp hX hFw z ⟨18 + st.val, by omega⟩
  have hoff : initOff ⟨18 + st.val, by omega⟩ = oOff st := by fin_cases st <;> rfl
  have hcnt : initCnt ⟨18 + st.val, by omega⟩ = 1 := by fin_cases st <;> rfl
  rw [hoff, hcnt] at hq
  refine ⟨show MBarrier.validCount 1 by decide, by simp, ⟨by simp, by simp⟩, by simp, by simp,
    fun r hr => ?_,
    fun r hr a ha hid => ?_, hq, by simp, fun v => no_inval hp hX hFw v _⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha =>
      obtain ⟨-, q, -, -, -, -, hl, hc1⟩ :=
        init_event hp hX hFw (Frame.lt_of_get hX he) he
      simp only [obj, Loc.mk.injEq, true_and] at hl
      obtain ⟨-, h1⟩ := initOff_o q st (by omega)
      exact .inl (by rw [ha, hc1, h1]; rfl)
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | arrive hid he ha =>
      rcases mism he rfl (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | increment hid he ha =>
      rcases mism he rfl (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases mism he hm (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | arriveOn hid he hm hn ha =>
      rcases mism he hm.symm (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | bulk hid he hcm hn ha =>
      rcases mism he hcm (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases mism he ⟨_, htg, hm⟩ (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | wait hid he ha =>
      rcases mism he rfl (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩
      · cases hk
      · simp only [Kind.wait.injEq] at hk
        obtain ⟨-, rfl, rfl, -, -⟩ := hk
        exact .inr (.inr (.inr ⟨_, _, hid, ha⟩))
    | commit hid he ht' ha =>
      rename_i i pc' sp rank'
      obtain ⟨h, k⟩ := i
      have hik := commit_same hp hX hFw hc ht he ht'
      simp only [Prod.mk.injEq] at hik
      obtain ⟨rfl, rfl⟩ := hik
      rw [hc] at he
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hr := target_rank ht ht'
      subst hr
      exact .inr (.inl ⟨_, List.mem_singleton_self _, hid, ha⟩)
  · simp only [List.mem_singleton] at ha
    subst ha
    cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | commit hid' he ht' ha' => exact ha'
    | init hid' _ _ | inval hid' _ _ | arrive hid' _ _ | wait hid' _ _ | increment hid' _ _ =>
      rw [hid'] at hid; cases hid
    | tensor hid' _ _ _ | arriveOn hid' _ _ _ _ | bulk hid' _ _ _ _ | clc hid' _ _ _ _ =>
      rw [hid'] at hid; cases hid

set_option maxHeartbeats 8000000 in
/-- Without an arrival record, the final O barrier's history is one-shot for any notification
id (it has no arrival). -/
theorem o_hist_none {st : Fin 2} {z : Nat} {R : AsyncCopy.Ref}
    (hR : ∃ i rank, R = .async i (.tcNotify rank))
    (hno : ∀ r ∈ X.objects (obj L z (oOff st)), ∀ c tx, r.action ≠ .arrive c tx) :
    MbarOneShot.Hist X (obj L z (oOff st)) [(R, 0)] [] := by
  have mism : ∀ {h k : Nat} {e : Event}, X.get (h, k) = some e →
      MbarOf e (obj L z (oOff st)) → (∀ c, e.kind ≠ .mbInit (obj L z (oOff st)) c) →
      (∃ sp, e.kind = .tc (.commit sp)) ∨
        (∃ ok, e.kind = .wait (obj L z (oOff st)) 0 ok true .cta) := by
    intro h k e he hm hni
    obtain ⟨σ, -, -, -, h2⟩ := o_event hp hX hFw he hm hni
    rcases h2 with ⟨d, n, sp, -, -, hk⟩ | ⟨d, n, ok, -, -, hk⟩
    · exact .inl ⟨sp, hk⟩
    · exact .inr ⟨ok, hk⟩
  have hq := obj_initFirst hp hX hFw z ⟨18 + st.val, by omega⟩
  have hoff : initOff ⟨18 + st.val, by omega⟩ = oOff st := by fin_cases st <;> rfl
  have hcnt : initCnt ⟨18 + st.val, by omega⟩ = 1 := by fin_cases st <;> rfl
  rw [hoff, hcnt] at hq
  refine ⟨show MBarrier.validCount 1 by decide, by simp, ⟨by simp, by simp⟩, by simp, by simp,
    fun r hr => ?_, fun r hr a ha hid => ?_, hq, by simp,
    fun v => no_inval hp hX hFw v _⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha =>
      obtain ⟨-, q, -, -, -, -, hl, hc1⟩ :=
        init_event hp hX hFw (Frame.lt_of_get hX he) he
      simp only [obj, Loc.mk.injEq, true_and] at hl
      obtain ⟨-, h1⟩ := initOff_o q st (by omega)
      exact .inl (by rw [ha, hc1, h1]; rfl)
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | arrive hid he ha => exact absurd ha (hno r hr _ _)
    | increment hid he ha =>
      rcases mism he rfl (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases mism he hm (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | arriveOn hid he hm hn ha => exact absurd ha (hno r hr _ _)
    | bulk hid he hcm hn ha =>
      rcases mism he hcm (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases mism he ⟨_, htg, hm⟩ (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩ <;> cases hk
    | wait hid he ha =>
      rcases mism he rfl (by intro c h; cases h) with ⟨sp, hk⟩ | ⟨ok, hk⟩
      · cases hk
      · simp only [Kind.wait.injEq] at hk
        obtain ⟨-, rfl, rfl, -, -⟩ := hk
        exact .inr (.inr (.inr ⟨_, _, hid, ha⟩))
    | commit hid he ht' ha => exact absurd ha (hno r hr _ _)
  · simp only [List.mem_singleton] at ha
    subst ha
    obtain ⟨i, rank, rfl⟩ := hR
    exfalso
    cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | commit hid' he ht' ha' => exact hno r hr _ _ ha'
    | init hid' _ _ | inval hid' _ _ | arrive hid' _ _ | wait hid' _ _ | increment hid' _ _ =>
      rw [hid'] at hid; cases hid
    | tensor hid' _ _ _ | arriveOn hid' _ _ _ _ | bulk hid' _ _ _ _ | clc hid' _ _ _ _ =>
      rw [hid'] at hid; cases hid

set_option maxHeartbeats 8000000 in
/-- **A successful parity-0 poll of a final O barrier follows a stage commit's notification**:
the object has an arrival record, a commit's. -/
theorem o_commit_exists {st : Fin 2} {z h k pc : Nat} {acq : Bool} {ws : MbarScope}
    (hw : X.get (h, k) = some ⟨pc, .wait (obj L z (oOff st)) 0 true acq ws⟩) :
    ∃ i pc' s rank, X.get i = some ⟨pc', .tc (.commit s)⟩ ∧
      TcCommit.target s rank = some (obj L z (oOff st)) := by
  by_contra hne
  have hno : ∀ r ∈ X.objects (obj L z (oOff st)), ∀ c tx, r.action ≠ .arrive c tx := by
    intro r hr c tx ha
    cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | commit hid he ht ha' => exact hne ⟨_, _, _, _, he, ht⟩
    | arrive hid he ha' =>
      obtain ⟨σ, -, -, -, h2⟩ := o_event hp hX hFw he rfl (by intro c h; cases h)
      rcases h2 with ⟨d, n, sp, -, -, hk⟩ | ⟨d, n, ok, -, -, hk⟩ <;> cases hk
    | arriveOn hid he hm hn ha' =>
      obtain ⟨σ, -, -, -, h2⟩ := o_event hp hX hFw he hm.symm
        (by intro c h; cases h)
      rcases h2 with ⟨d, n, sp, -, -, hk⟩ | ⟨d, n, ok, -, -, hk⟩ <;> cases hk
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | increment _ _ ha' | tensor _ _ _ ha'
    | bulk _ _ _ _ ha' | clc _ _ _ _ ha' => rw [ha'] at ha; cases ha
  have ht := o_hist_none hp hX hFw (R := .async (0, 0) (.tcNotify 0))
    ⟨_, _, rfl⟩ hno
  have hu := ht.observes_arrive hX (List.mem_singleton_self _) hw
  obtain ⟨i, j, r, w, phase, hr, hid, -⟩ := hu
  have hrm : r ∈ X.objects (obj L z (oOff st)) := List.mem_of_getElem? hr
  cases AsyncCopy.record_source hX.tma.2.2.1 hrm with
  | commit hid' he ht' ha' => exact hno r hrm _ _ ha'
  | init hid' _ _ | inval hid' _ _ | arrive hid' _ _ | wait hid' _ _ | increment hid' _ _ =>
    rw [hid'] at hid; cases hid
  | tensor hid' _ _ _ | arriveOn hid' _ _ _ _ | bulk hid' _ _ _ _ | clc hid' _ _ _ _ =>
    rw [hid'] at hid; cases hid

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
