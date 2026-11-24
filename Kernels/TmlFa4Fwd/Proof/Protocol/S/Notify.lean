-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
public import Lemmas.Protocol.UnitNotify
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ring
import Kernels.TmlFa4Fwd.Proof.Protocol.S.Obj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The S-full barriers are completed by one lane's commits

Every commit to stage `st`'s S-full barrier (`80 + 8 st`) of a CTA is of the one lane of warp 12
that wins the warp's elections, so the barrier is a commit object of that lane (`sNotify`,
`MbarRing.Notify.Obj`), polled by the stage's softmax lanes with the parity of their earlier
polls (`s_poll`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}
  (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A poll of an S-full barrier** is a softmax lane's of the stage. -/
theorem s_poll (st : Fin 2) {h k pc par : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .wait (obj L g (80 + 8 * st.val)) par ok acq sc⟩) :
    par % 2 = okPolls (obj L g (80 + 8 * st.val)) ((X.tr h).take k) % 2 ∧ acq = true ∧ sc = .cta ∧
      h / L.block = g / L.block ∧ Prologue.warpIndex L h < 8 ∧
      Prologue.warpIndex L h / 4 = st.val := by
  obtain ⟨hc, hu⟩ := bar_use (o := 80 + 8 * st.val) hp hX hFw he rfl (fun _ h => by cases h)
  cases hu with
  | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
  | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
  | epiPoll _ _ _ ho | corrPoll _ _ ho => omega
  | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
  | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
  | softPoll a ok' hw ha ho hk =>
    have ha' : a = 80 := by omega
    subst ha'
    simp only [Kind.wait.injEq] at hk
    obtain ⟨-, rfl, -, hacq, hsc⟩ := hk
    refine ⟨?_, hacq, hsc, hc, hw, by omega⟩
    simp [softΔ]

/-- **A commit to a barrier of a CTA**: a lane of its warp 12, which won an election. -/
theorem mma_commit_of {o h k pc : Nat} {s : TcCommit.Spec} {rank : Fin 16}
    (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩)
    (ht : TcCommit.target s rank = some (obj L g o)) :
    h < L.threads ∧ h / L.block = g / L.block ∧ Prologue.warpIndex L h = 12 ∧
      s.mbar = obj L g o ∧ ∃ j pc' inst, j < k ∧
        X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩ := by
  obtain ⟨hc, hu⟩ := bar_use (o := o) hp hX hFw he ⟨rank, ht⟩ (fun _ h => by cases h)
  cases hu with
  | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | epiPoll _ _ _ _ hk
  | corrPoll _ _ _ hk | mmaPoll _ _ _ hk | softPoll _ _ _ _ _ hk | ldPoll _ _ _ _ hk
  | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
  | mmaCommit s' hw _ hk hb _ hel =>
    cases hk
    exact ⟨Frame.lt_of_get hX he, hc, hw, hb, hel⟩

/-- Two lanes that commit to barriers of one CTA are one lane. -/
theorem mma_commit_lane {o o' h h' k k' pc pc' : Nat} {s s' : TcCommit.Spec} {rank rank' : Fin 16}
    (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩)
    (ht : TcCommit.target s rank = some (obj L g o))
    (he' : X.get (h', k') = some ⟨pc', .tc (.commit s')⟩)
    (ht' : TcCommit.target s' rank' = some (obj L g o')) : h = h' := by
  obtain ⟨hl, hc, hw, -, j, pcj, ij, -, hj⟩ := mma_commit_of hp hX hFw he ht
  obtain ⟨hl', hc', hw', -, j', pcj', ij', -, hj'⟩ := mma_commit_of hp hX hFw he' ht'
  refine won_unique hX ⟨⟨hl, hl', hc.trans hc'.symm⟩, ?_⟩ hj hj'
  simp only [Prologue.warpIndex] at hw hw' ⊢
  omega

/-- **Stage `st`'s S-full barrier is a commit object** of one lane. -/
theorem sNotify_lane (g : Nat) (st : Fin 2) :
    ∃ c, MbarRing.Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0 ∧
      ∀ (i : EvId) (pc : Nat) (sp : TcCommit.Spec) (r : Fin 16),
        X.get i = some ⟨pc, .tc (.commit sp)⟩ →
        TcCommit.target sp r = some (obj L g (80 + 8 * st.val)) → i.1 = c := by
  obtain ⟨q, hq, hcn⟩ := sfull_init (o := 80 + 8 * st.val) (by unfold SOff; omega)
  have hinit : PairTmaRing.InitFirst X (obj L g (80 + 8 * st.val)) 1 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hcn] at this
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (obj L g (80 + 8 * st.val)))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g (80 + 8 * st.val)) c) =>
    sfull_use hp hX hFw (by unfold SOff; omega) he hm hni
  obtain ⟨c, hcl⟩ : ∃ c, ∀ (i : EvId) (pc : Nat) (sp : TcCommit.Spec) (r : Fin 16),
      X.get i = some ⟨pc, .tc (.commit sp)⟩ →
      TcCommit.target sp r = some (obj L g (80 + 8 * st.val)) → i.1 = c := by
    by_cases hex : ∃ (i : EvId) (pc : Nat) (sp : TcCommit.Spec) (r : Fin 16),
        X.get i = some ⟨pc, .tc (.commit sp)⟩ ∧
        TcCommit.target sp r = some (obj L g (80 + 8 * st.val))
    · obtain ⟨i, pc, sp, r, he, ht⟩ := hex
      exact ⟨i.1, fun i' pc' sp' r' he' ht' => mma_commit_lane hp hX hFw (h := i'.1) (k := i'.2)
        (h' := i.1) (k' := i.2) he' ht' he ht⟩
    · exact ⟨0, fun i pc sp r he ht => absurd ⟨i, pc, sp, r, he, ht⟩ hex⟩
  refine ⟨c, MbarRing.Notify.Obj.of_commits hX hinit (fun {h i pc tx cnt rel sc} he => ?_)
    (fun {i pc a sp} he hm => ?_) (fun {i pc s} he hm => ?_) (fun {i pc m' noinc} he hm => ?_)
    (fun {i pc sp tg} he => no_clc hp hX hFw i.1 i.2 pc sp tg he)
    (fun {i pc m'} he => no_inval hp hX hFw i m' ⟨pc, he⟩)
    (fun {i pc sp r} he ht => ⟨hcl i pc sp r he ht,
      (mma_commit_of hp hX hFw (h := i.1) (k := i.2) he ht).2.2.2.1⟩)
    (fun {h k pc par acq sc} he => by have := (s_poll hp hX hFw st he).1; omega)
    (Nat.zero_le _), hcl⟩
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · subst hm
    rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk

theorem sNotify (g : Nat) (st : Fin 2) :
    ∃ c, MbarRing.Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0 :=
  let ⟨c, h, _⟩ := sNotify_lane hp hX hFw g st
  ⟨c, h⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
