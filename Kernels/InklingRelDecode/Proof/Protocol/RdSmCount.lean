-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSmOdone
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmExec
public import Kernels.InklingRelDecode.Proof.Interface.RdDPred
public import Kernels.InklingRelDecode.Proof.Interface.SvTrace
public import Kernels.InklingRelDecode.Proof.Interface.ShapeOdone

@[expose] public section

/-!
# The softmax thread's polls of `s_ready` and `o_done`, counted along its states

The counts of `SOSmRun` and `SOSmOdone` are along an anchored run of the softmax region's machine
(`SO.SmRunAt`, which the composed thread does not give directly: the thread's trace continues
into the epilogue). Here the same counts are proved by induction over the thread's states
`St Q L X g k` (`Interface.pred_d`), so no anchor is a premise: at a state before the region
(`Interface.PreSt`: the common start and the prologue) no poll of either barrier has happened (no
poll site of the program is a pre-region site), and the region's first state has the counts `0`.

* `SmCnt`: the successful polls of `s_ready b` before the `k`-th event number
  `below2 b (smPolled d)`, those of `o_done` number `smOPolled d`, and `OdoneOk d`.
* `sm_cnt`: it holds at every softmax state of a launched thread, and at every state before the
  region no poll of either barrier has happened.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rd
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.SO
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The poll sites -/

theorem dstart_pc_notWait (s : DStart.Site) : s.pc ∉ waitSites := by
  cases s
  all_goals decide +kernel

theorem pro_pc_notWait (s : ProA.Site) : s.pc ∉ waitSites := by
  cases s
  all_goals decide +kernel

/-- **A poll event fires from a state at a poll site.** -/
theorem poll_pc (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) {k : Nat}
    {e : Event} {s : TSt} (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s))
    {l : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait l p ok acq sc) :
    TSt.pc s ∈ waitSites := by
  obtain ⟨t, ins, o, -, -, hc, hf'⟩ := Frame.fired_site hf.sound hX he hσ
  by_contra hn
  exact fires_notWait (eventTmpl_notWait (fun p b o par a s h => hn (wait_pc hc h))) hf'
    l p ok acq sc hk

/-- The events fired at a pre-region state are no polls. -/
theorem pre_notWait (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k : Nat} {e : Event} {s : DComp.St} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d s))) (hs : PreSt s) :
    ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc := by
  intro l p ok acq sc hk
  have := poll_pc hX hf he hσ hk
  cases s with
  | dstart d => exact dstart_pc_notWait d.site this
  | pro d => exact pro_pc_notWait d.site this
  | sm d => exact hs
  | epi d => exact hs

/-! ### The poll shape at `waitO` -/

/-- **`WaitOShape` from the launch's shared-memory bounds.** -/
theorem waitOShape_of (hS : Sm.SharedOk L) : WaitOShape L := by
  intro g d e u hF hs
  obtain ⟨ok, h⟩ := Sm.shape_waitO hS hF hs
  refine ⟨ok, ?_⟩
  rw [h, loc_oDone]
  rfl

/-! ### The counts -/

/-- The counts at a softmax state before the `k`-th event. -/
structure SmCnt (L : Launch) (X : Execution) (g k : Nat) (d : Sm.D) : Prop where
  s : ∀ b < 2, okPolls (sReady L (g / L.block) b) ((X.tr g).take k) = below2 b (smPolled d)
  o : okPolls (oDone L (g / L.block)) ((X.tr g).take k) = smOPolled d
  ok : OdoneOk d

/-- The counts at a state before the softmax region: no poll yet. -/
structure PreCnt (L : Launch) (X : Execution) (g k : Nat) : Prop where
  s : ∀ b < 2, okPolls (sReady L (g / L.block) b) ((X.tr g).take k) = 0
  o : okPolls (oDone L (g / L.block)) ((X.tr g).take k) = 0

theorem okPolls_take_succ (m : Loc) {l : List Event} {k : Nat} {e : Event}
    (he : l[k]? = some e) :
    okPolls m (l.take (k + 1)) = okPolls m (l.take k) + (if okPoll m e = true then 1 else 0) := by
  unfold okPolls
  rw [List.take_add_one, he]
  simp [List.countP_append]

/-- One step of the region on the counts of `s_ready`. -/
theorem sm_step_s (hS : Sm.SharedOk L) (hW : WaitOShape L) {d d' : Sm.D} {e : Event} {u : TState}
    (hF : Sm.Fired L g d e (some u)) (hn : Sm.next L g d e = some (some d')) {b : Nat}
    (hb : b < 2) :
    below2 b (smPolled d') = below2 b (smPolled d) +
      (if okPoll (sReady L (g / L.block) b) e = true then 1 else 0) := by
  have hpol := sm_next_polled hn
  have hokp := sm_okPoll_s hS hW hF hb
  rw [hokp, hpol]
  by_cases hw : d.site = .waitS
  · have hp : smPolled d = d.i := by simp [smPolled, hw]
    by_cases hok : okW e = true
    · by_cases hm : d.i % 2 = b
      · simp [hw, hok, hm, hp, below2_succ hb]
      · simp [hw, hok, hm, hp, below2_succ hb]
    · simp [hw, hok]
  · simp [hw]

/-- One step of the region on the counts of `o_done`. -/
theorem sm_step_o (hS : Sm.SharedOk L) (hW : WaitOShape L) {d d' : Sm.D} {e : Event} {u : TState}
    (hF : Sm.Fired L g d e (some u)) (hn : Sm.next L g d e = some (some d')) (hd : OdoneOk d) :
    OdoneOk d' ∧ smOPolled d' = smOPolled d +
      (if okPoll (oDone L (g / L.block)) e = true then 1 else 0) := by
  obtain ⟨h1, hc⟩ := sm_next_odone hd hn
  refine ⟨h1, ?_⟩
  rw [hc, sm_okPoll_o hS hW hF]
  by_cases hw : d.site = .waitO <;> by_cases hk : okW e = true <;> simp [hw, hk]

/-- **The counts along the thread's states.** At every state of a launched thread before the
region no poll of `s_ready` or `o_done` has happened, and at every softmax state the successful
polls are those of `SmCnt`. -/
theorem sm_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) :
    ∀ (k : Nat), k ≤ (X.tr g).length → ∀ s : DComp.St,
      St Q L X g k = some (some (.d s)) →
      (PreSt s → PreCnt L X g k) ∧ ∀ d, s = .sm d → SmCnt L X g k d := by
  have hS := ProA.sharedOk_of_pre hpre
  have hW := waitOShape_of hS
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk s hσ
    rcases pred_d hk hσ with ⟨rfl, rfl⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
    · refine ⟨fun _ => ⟨fun b _ => by simp [okPolls], by simp [okPolls]⟩, ?_⟩
      intro d hd
      cases hd
    · have hk0 : k0 ≤ (X.tr g).length := by omega
      have hge : X.get (g, k0) = some e := he
      obtain ⟨hp0, hs0⟩ := ih k0 (by omega) hk0 s0 hσ0
      -- the event at the state before
      have hev : ∀ (m : Loc), (PreSt s0 → okPoll m e = false) := by
        intro m hpre0
        exact okPoll_notWait (pre_notWait hX hf hge hσ0 hpre0)
      refine ⟨fun hpr => ?_, fun d hd => ?_⟩
      · have hpre0 := dnext_pre hn hpr
        have hp := hp0 hpre0
        refine ⟨fun b hb => ?_, ?_⟩
        · rw [okPolls_take_succ _ he, hp.s b hb, hev _ hpre0]; rfl
        · rw [okPolls_take_succ _ he, hp.o, hev _ hpre0]; rfl
      · subst hd
        rcases dnext_sm hn with ⟨dp, rfl, rfl⟩ | ⟨d0, rfl, hn0⟩
        · have hp := hp0 trivial
          refine ⟨fun b hb => ?_, ?_, ?_⟩
          · rw [okPolls_take_succ _ he, hp.s b hb, hev _ trivial]
            simp [smPolled, SmEntry.d0, below2_zero]
          · rw [okPolls_take_succ _ he, hp.o, hev _ trivial]
            simp [smOPolled, SmEntry.d0]
          · simp [OdoneOk, SmEntry.d0]
        · have hc := hs0 d0 rfl
          obtain ⟨u, hF⟩ := fired_cont hX hf hg hge hσ0 (by simp [ExitState])
          have hF' := fired_sm hF
          obtain ⟨h1, h2⟩ := sm_step_o hS hW hF' hn0 hc.ok
          refine ⟨fun b hb => ?_, ?_, h1⟩
          · rw [okPolls_take_succ _ he, hc.s b hb, sm_step_s hS hW hF' hn0 hb]
          · rw [okPolls_take_succ _ he, hc.o, h2]

end
end PTX.Kernels.InklingRelDecode.Proof.Rd
