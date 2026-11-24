-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU
public import Kernels.TmlFa4Fwd.Proof.Lib.ProxyFence
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageBar
public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Softmax.BiasAddr
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Lemmas.Flow.NotBulk
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Places

@[expose] public section

/-! # The softmax warps' bias reads and the fence before their stage barrier

The event before a stage-barrier event is a `fence.proxy.async.shared::cta` (`soft_stage_fence`). A
bias read is of one word of the lane's row in one of the stage's two boxes, after one more poll of
the bias slot than stage-barrier events (`soft_bias_read`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (before inBias inPlain ptsOf passed RefQ)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

/-- Only a fence leads to a stage barrier. -/
private theorem bsync_pred : ∀ b : Bool, Softmax.allSites.all (fun s =>
    (Softmax.nexts b s).all fun s' => match s' with
      | .bsync _ => match s with | .fence _ => true | _ => false
      | _ => true) = true := by
  intro b; cases b <;> decide +kernel

private theorem bld_tab (b : Bool) :
    (∀ c : Fin 16, (ptsOf b (.acquire 320)).countP (before (.bld false c)) = 1 ∧
      (ptsOf b .sb).countP (before (.bld false c)) = 0 ∧
      (ptsOf b (.acquire 320)).countP (before (.bld true c)) = 2 ∧
      (ptsOf b .sb).countP (before (.bld true c)) = 1) ∧
    [(ptsOf b (.acquire 320)).countP inBias, (ptsOf b (.acquire 320)).countP inPlain,
      (ptsOf b .sb).countP inBias, (ptsOf b .sb).countP inPlain] = [1, 0, 1, 0] := by
  cases b <;> decide +kernel

private theorem stage_id' (hw : Prologue.warpIndex L h < 8) :
    (if Softmax.stg L h then 12 else 11) = stageId (Prologue.warpIndex L h / 4) := by
  have hs : Softmax.stg L h = decide (4 ≤ Prologue.warpIndex L h) := by
    have key : ∀ w < 8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4 ≤ w) := by decide
    exact key _ hw
  rw [hs]
  unfold stageId
  by_cases h4 : 4 ≤ Prologue.warpIndex L h
  · simp only [h4, decide_true, ↓reduceIte]; omega
  · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

private theorem isStage' (hw : Prologue.warpIndex L h < 8) :
    ((X.tr h).take k).countP (Execution.isBarId (stageId (Prologue.warpIndex L h / 4))) =
      ((X.tr h).take k).countP (cls L h (.soft .sb)) := by
  refine List.countP_congr fun e _ => ?_
  have hw' : h % L.block / 32 < 8 := hw
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Execution.isBarId, cls, Softmax.cls, Softmax.Cnt.pointed, hw',
    stage_id' hw]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The event before a stage-barrier event** is a proxy fence of the CTA's shared bytes. -/
theorem soft_stage_fence (hw : Prologue.warpIndex L h < 8) {pc id : Nat} {cnt : Option Nat}
    {mode : BarMode} (hid : id = 11 ∨ id = 12) (he : X.get (h, k) = some ⟨pc, .bar id cnt mode⟩) :
    ∃ i pcf, k = i + 1 ∧
      X.get (h, i) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  have hub : ∀ f, (⟨pc, .bar id cnt mode⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | enter r => simp [exit] at hi
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
    | fence => simp only [Startup.Ev] at hev; cases hev
    | bar =>
      simp only [Startup.Ev, Kind.bar.injEq] at hev
      omega
    | elect j =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  obtain ⟨b, hs⟩ : ∃ b, d.site = .bsync b := by
    rcases soft_bar_site hev.1 with ⟨-, rfl, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, -, -⟩
    · omega
    · exact h1
    · exfalso
      rw [soft_nbW hw] at hid
      omega
  have hkl : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  cases k with
  | zero =>
    rw [Frame.stateAt_zero] at hσ
    cases hσ
  | succ i =>
    obtain ⟨e', he'⟩ : ∃ e', X.get (h, i) = some e' :=
      ⟨_, List.getElem?_eq_getElem (show i < (X.tr h).length by omega)⟩
    have hst := Frame.stateAt_succ (C := thread p L) (show (X.tr h)[i]? = some e' from he')
    rw [hσ] at hst
    have hub' : ∀ f, e'.kind ≠ .ub f := by
      intro f hk
      cases hs0 : Frame.stateAt (thread p L) X h i with
      | none => rw [hs0] at hst; simp at hst
      | some o =>
        cases o with
        | none =>
          rw [hs0] at hst
          exact absurd hst (by simp [Flow.Code.toMachine])
        | some σ0 =>
          rw [hs0] at hst
          have hn : (thread p L h).next σ0 e' = some (some (SmWarp.sinj p L h d n)) := hst.symm
          obtain ⟨σ1, n0⟩ := σ0
          obtain ⟨-, hn2⟩ := Code.counted_next_some hn
          simp only at hn2
          rw [hn2] at h0
          simp [Code.bump, cls, hk] at h0
    rcases SmWarp.open_ev hp hX hFw hw he' hub' with ⟨s, n0, hσ', -, -, hi, hev'⟩ |
      ⟨d0, n0, hσ', h0', hR', hinv, hev'⟩
    · exfalso
      rw [hσ'] at hst
      have hn : (thread p L h).next (.inl s, n0) e' = some (some (SmWarp.sinj p L h d n)) :=
        hst.symm
      obtain ⟨h1, -⟩ := Code.counted_next_some hn
      simp only [glued, Code.glue, Startup.code] at h1
      cases hsu : Startup.succ L h s e' with
      | none => rw [hsu] at h1; simp at h1
      | some o =>
        cases o with
        | none => rw [hsu] at h1; simp at h1
        | some s' =>
          rw [hsu] at h1
          simp only [Option.map_some, Option.some.injEq, Code.enter] at h1
          split at h1
          · rename_i r _
            cases r <;> cases h1
            cases hs
          · cases h1
    · rw [hσ'] at hst
      have hn : (thread p L h).next (SmWarp.sinj p L h d0 n0) e' =
          some (some (SmWarp.sinj p L h d n)) := hst.symm
      obtain ⟨h1, -⟩ := Code.counted_next_some hn
      change Option.map (Option.map fun d' => (Sum.inr ⟨Role.softmax, d'⟩ : (glued p L h).D))
        ((frag p L h .softmax).next d0 e') = _ at h1
      cases hr : (frag p L h .softmax).next d0 e' with
      | none => rw [hr] at h1; simp at h1
      | some o =>
        cases o with
        | none => rw [hr] at h1; simp at h1
        | some d1 =>
          rw [hr] at h1
          simp only [Option.map_some, Option.some.injEq] at h1
          cases h1
          have hsc : Softmax.Control.succ p L h d0 e' = some (some d) := hr
          have hfence : ∃ b, d0.site = .fence b := by
            rcases Softmax.Control.succ_places hsc with ⟨hs', -⟩ | hM
            · exfalso
              change d.site = d0.site at hs'
              have h0 : d0.site = .bsync b := hs'.symm.trans hs
              obtain ⟨s,v,kk,ac⟩ := d0
              change s = _ at h0
              subst s
              simp only [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ,
                Option.map_some, Option.some.injEq] at hsc
              rw [← hsc] at hs
              cases b <;> unfold Softmax.D.ite at hs <;> split at hs <;> cases hs
            · have h1 := List.all_eq_true.mp (bsync_pred (Softmax.lz L h)) d0.site
                (Softmax.mem_allSites _)
              have h2 := List.all_eq_true.mp h1 d.site hM.1
              rw [hs] at h2
              revert h2
              cases d0.site <;> simp
          obtain ⟨b', hs0⟩ := hfence
          have hk : ∃ f sc, e'.kind = .fenceProxy f sc := by
            have := hev'.1
            unfold Softmax.Ev at this
            rw [show d0.scheduler.site = d0.site from rfl, hs0] at this
            exact this
          obtain ⟨f, sc, hk⟩ := hk
          obtain ⟨pcf, kd⟩ := e'
          simp only at hk
          subst hk
          obtain ⟨rfl, rfl⟩ := proxy_fence hX he'
          exact ⟨i, pcf, rfl, he'⟩

/-- **A bias read**: of one word of the lane's row in one of its stage's two boxes, after one more
poll of the bias slot than stage-barrier events. -/
theorem soft_bias_read {e : Event} (he : X.get (h, k) = some e)
    {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X h k = some (some (SmWarp.sinj p L h d n)))
    {b : Bool} {c : Fin 16} (hs : d.site = .bld b c) {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .rd a bs) :
    h < L.threads ∧ Prologue.warpIndex L h < 8 ∧
      okPolls (sobj L h 320) ((X.tr h).take k) =
        ((X.tr h).take k).countP
          (Execution.isBarId (stageId (Prologue.warpIndex L h / 4))) + 1 ∧
      a.size = 4 ∧ a.loc.space = .shared ∧ a.loc.cta = h / L.block ∧ a.loc.addr % 4 = 0 ∧
      ∃ q : Fin 2, a.loc.addr / 128 =
        (L.sharedBase + 128 * (h % L.block % 128) + 32768 * (Prologue.warpIndex L h / 4) +
          166912 + 16384 * q.val) / 128 := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hh := Frame.lt_of_get hX he
  obtain ⟨σ', n', hσ', -, hJ, -, -⟩ := ev_open hp hX hFw he hub
  rw [hσ] at hσ'
  cases hσ'
  have hw : Prologue.warpIndex L h < 8 := (JR.softmax hJ).1
  obtain ⟨ts, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n1, hs1, -⟩ | ⟨d1, n1, hσ1, h0, hR, -, hev⟩
  · rw [hσ] at hs1; cases hs1
  rw [hσ] at hσ1
  cases hσ1
  obtain ⟨⟨cc, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR.2 h0
  have hcnt : ∀ c', Softmax.Cnt.pointed c' = true →
      ((X.tr h).take k).countP (cls L h (.soft c')) = cc c' := fun c' hc' => by
    rw [count hσ, ← hLk c' hc']
  refine ⟨hh, hw, ?_, ?_⟩
  · rw [isStage' hw, soft_okPolls hw, hcnt _ rfl, hcnt _ rfl]
    obtain ⟨t1, t2⟩ := bld_tab (Softmax.lz L h)
    simp only [List.cons.injEq, and_true] at t2
    obtain ⟨a1, a2, a3, a4⟩ := t1 c
    have e1 := hQ.cnt (.acquire 320) rfl
    have e2 := hQ.cnt .sb rfl
    simp only [Softmax.Control.D.scheduler] at e1 e2
    rw [e1, e2, hs]
    cases b <;> simp only [passed, t2, a1, a2, a3, a4] <;> omega
  · obtain ⟨site, v, kk, ac⟩ := d
    simp only at hs
    subst hs
    obtain ⟨b1, b2, b3, b4, q, b5⟩ := Softmax.bld_acc hp hw (b := b) (c := c)
      (v := v.scheduler) (k := kk) (ac := ac) hat hc hf hk
    exact ⟨b1, b2, b3, b4, q, b5⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
