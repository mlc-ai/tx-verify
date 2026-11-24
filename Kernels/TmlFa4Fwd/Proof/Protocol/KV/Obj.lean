-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Lib.OutputSlots
public import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Protocol.CpAsyncPhase
public import Lemmas.Protocol.TmaUnit
public import Lemmas.Protocol.TmaUnitBlock
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # The K/V ring's full barriers

The full barriers of the K/V ring (shared offsets 32, 40, 48, count 64) are named only by polls
(the MMA warp's and the loader warps') and the loader lanes' `cp.async.mbarrier.arrive.noinc`
(`kv_use`), so each is an object of no-increment arrive-ons (`kvObj`,
`MbarRing.NoIncObject`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The K/V ring's full barriers. -/
abbrev KvOff (o : Nat) : Prop := o = 32 ∨ o = 40 ∨ o = 48

/-- The loader lanes of lane `g`'s CTA. -/
def LdLane (L : Launch) (g h : Nat) : Prop :=
  h / L.block = g / L.block ∧ (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)

/-- **Who names a K/V full barrier**: a poll, or a loader lane's no-increment arrive-on. -/
theorem kv_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k o : Nat}
    {e : Event} (ho : KvOff o) (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) :
    (∃ par ok acq sc, e.kind = .wait (obj L g o) par ok acq sc) ∨
      LdLane L g h ∧ e.kind = .asyncArrive (obj L g o) true := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  cases hu with
  | epiArr _ _ ho' | corrArr _ ho' | softArr _ _ _ ho' => omega
  | ldArr _ _ ho' | ldCopy _ _ _ ho' => unfold LdTmaOff at ho'; omega
  | mmaCommit _ _ ho' => unfold MmaCommitOff at ho'; omega
  | epiPoll _ ok _ _ hk | corrPoll ok _ _ hk | softPoll _ ok _ _ _ hk | mmaPoll ok _ _ hk
  | ldPoll _ ok _ _ hk => exact .inl ⟨_, ok, true, .cta, hk⟩
  | ldAsync hw _ hk => exact .inr ⟨⟨hc, hw⟩, hk⟩

set_option hygiene false in
/-- Split a shape hypothesis on a CLC request into its cases and close them. -/
macro "noclc_close" : tactic => `(tactic| (
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try simp_all [Epilogue.isStore, Correction.rdOrUb, Softmax.rdOrUb,
    Softmax.tcLdOrUb])))

set_option maxHeartbeats 4000000 in
theorem epi_noclc {d : Epilogue.D} {pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hev : Epilogue.Ev p L g d ⟨pc, .clcIssue sp tg⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Epilogue.Ev] at hev
  noclc_close

set_option maxHeartbeats 4000000 in
theorem corr_noclc {d : Correction.D} {pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hev : Correction.Ev p L g d ⟨pc, .clcIssue sp tg⟩) : False := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  all_goals first | exact epi_noclc hev | skip
  noclc_close

set_option maxHeartbeats 4000000 in
theorem soft_noclc {d : Softmax.D} {pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hev : Softmax.Ev p L g d ⟨pc, .clcIssue sp tg⟩) : False := by
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals first | exact epi_noclc hev | skip
  noclc_close

set_option maxHeartbeats 4000000 in
theorem mma_noclc {d : Mma.D} {pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hev : Mma.Ev p L g d ⟨pc, .clcIssue sp tg⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Mma.Ev] at hev
  all_goals first | exact epi_noclc hev | skip
  noclc_close

set_option maxHeartbeats 4000000 in
theorem ld_noclc {w : Nat} {d : Loader.D} {pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hev : Loader.Ev p L g w d ⟨pc, .clcIssue sp tg⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first | exact epi_noclc hev | skip
  noclc_close

set_option maxHeartbeats 4000000 in
/-- **No event is a CLC request.** -/
theorem no_clc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    ∀ h k pc sp tg, X.get (h, k) ≠ some ⟨pc, .clcIssue sp tg⟩ := by
  intro h k pc sp tg he
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have hh := Frame.lt_of_get hX he
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hh he
    (fun f hf => by cases hf)
  have hJ' : JR p L h (σ1, n) := hJ
  rcases σ1 with s | ⟨i, d⟩
  · have hEv : Startup.Ev L h s ⟨pc, .clcIssue sp tg⟩ := hev
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | enter r => exact jr_start_site hJ' r rfl
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;> cases hk
    | fence => simp only [Startup.Ev] at hEv; cases hEv
    | bar => simp only [Startup.Ev] at hEv; cases hEv
    | elect j =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  cases i with
  | epilogue => exact epi_noclc hev
  | correction => exact corr_noclc (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,hv⟩; cases hv))
  | softmax => exact soft_noclc hev.1
  | loader b => exact ld_noclc hev
  | mma =>
    rcases d with s | ⟨_, d⟩
    · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
    · exact mma_noclc hev
  | stub r =>
    simp only [JR_eq] at hJ'
    split_ifs at hJ'
    · exact hJ'
    · unfold RefAll at hJ'
      split_ifs at hJ' <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]


theorem kv_init {o : Nat} (ho : KvOff o) :
    ∃ q : Fin 34, initOff q = o ∧ initCnt q = 64 := by
  rcases ho with rfl | rfl | rfl
  · exact ⟨4, rfl, rfl⟩
  · exact ⟨5, rfl, rfl⟩
  · exact ⟨6, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **A K/V full barrier is an object of no-increment arrive-ons** with count 64. -/
theorem kvObj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : KvOff o)
    (g : Nat) : MbarRing.NoIncObject X (obj L g o) 64 := by
  obtain ⟨q, hq, hc⟩ := kv_init ho
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) =>
    kv_use hp hX hFw ho he hm hni
  have hinit : PairTmaRing.InitFirst X (obj L g o) 64 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hc] at this
  refine MbarRing.NoIncObject.of_issues hX hinit (fun i h => no_inval hp hX hFw i _ h)
    (fun ⟨h, k⟩ tx c rel sc ⟨pc, he⟩ => ?_) (fun ⟨h, k⟩ ⟨pc, he⟩ => ?_)
    (fun ⟨h, k⟩ addr sp ⟨pc, he⟩ hm => ?_) (fun ⟨h, k⟩ s ⟨pc, he⟩ hm => ?_)
    (fun ⟨h, k⟩ s rank ⟨pc, he⟩ hm => ?_) (fun ⟨h, k⟩ sp tg c ⟨pc, he⟩ hm => ?_)
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨-, hk⟩ <;> cases hk
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨-, hk⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨-, hk⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨-, hk⟩ <;> cases hk
  · rcases hU he ⟨_, hm⟩ (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨-, hk⟩ <;> cases hk
  · exact no_clc hp hX hFw h k pc sp tg he

/-! ### The Q stages' full barriers -/

/-- The Q stages' full barriers. -/
abbrev QOff (o : Nat) : Prop := o = 0 ∨ o = 8

/-- **Who names a Q stage's full barrier**: a poll, a loader lane's expect-tx arrival, or a
loader's tensor copy. -/
theorem q_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k o : Nat}
    {e : Event} (ho : QOff o) (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) :
    (∃ par ok acq sc, e.kind = .wait (obj L g o) par ok acq sc) ∨
      (LdLane L g h ∧ ∃ tx, e.kind = .arrive (obj L g o) tx 1 true .cta) ∨
      ∃ a sp, e.kind = .tensorIssue a sp ∧ sp.mbar = obj L g o := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  cases hu with
  | epiArr _ _ ho' | corrArr _ ho' | softArr _ _ _ ho' | ldAsync _ ho' => omega
  | mmaCommit _ _ ho' => unfold MmaCommitOff at ho'; omega
  | epiPoll _ ok _ _ hk | corrPoll ok _ _ hk | softPoll _ ok _ _ _ hk | mmaPoll ok _ _ hk
  | ldPoll _ ok _ _ hk => exact .inl ⟨_, ok, true, .cta, hk⟩
  | ldArr tx hw _ hk => exact .inr (.inl ⟨⟨hc, hw⟩, tx, hk⟩)
  | ldCopy a s _ _ hk hb => exact .inr (.inr ⟨a, s, hk, hb⟩)

theorem q_init {o : Nat} (ho : QOff o) : ∃ q : Fin 34, initOff q = o ∧ initCnt q = 1 := by
  rcases ho with rfl | rfl
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **A Q stage's full barrier is a one-CTA TMA unit object** of the CTA's loader lanes. -/
theorem qObj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : QOff o)
    (g : Nat) : MbarRing.TmaUnitObject X (obj L g o) (LdLane L g) := by
  obtain ⟨q, hq, hc⟩ := q_init ho
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) =>
    q_use hp hX hFw ho he hm hni
  have hinit : PairTmaRing.InitFirst X (obj L g o) 1 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hc] at this
  refine MbarRing.TmaUnitObject.of_issues hX hinit
    (fun i h => no_inval hp hX hFw i _ h)
    (fun h k pc tx c rel sc he => ?_) (fun ⟨h, k⟩ noinc ⟨pc, he⟩ => ?_)
    (fun ⟨h, k⟩ s ⟨pc, he⟩ hm => ?_) (fun ⟨h, k⟩ s rank ⟨pc, he⟩ hm => ?_)
    (fun ⟨h, k⟩ sp tg c ⟨pc, he⟩ hm => ?_)
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hl, tx', hk⟩ |
      ⟨_, _, hk, _⟩
    · cases hk
    · simp only [Kind.arrive.injEq] at hk
      obtain ⟨-, -, rfl, rfl, -⟩ := hk
      exact ⟨hl, rfl, rfl⟩
    · cases hk
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ |
      ⟨_, _, hk, _⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ |
      ⟨_, _, hk, _⟩ <;> cases hk
  · rcases hU he ⟨_, hm⟩ (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ |
      ⟨_, _, hk, _⟩ <;> cases hk
  · exact no_clc hp hX hFw h k pc sp tg he

end
end PTX.Kernels.TmlFa4Fwd.Proof
