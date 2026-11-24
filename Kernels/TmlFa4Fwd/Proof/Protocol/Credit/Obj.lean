-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Lemmas.Protocol.UnitObject
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # The statistics-credit barriers

The credit barriers (shared offsets 192 and 200, count 128) are named only by polls (the softmax
warps') and the correction lanes' unit arrivals (`credit_use`): the correction warps hand the
statistics slot of a stage back to its softmax warps after reading it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The statistics-credit barriers. -/
abbrev CreditOff (o : Nat) : Prop := o = 192 ∨ o = 200

/-- **Who names a statistics-credit barrier**: a poll, or a correction lane's unit arrival. -/
theorem credit_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k o : Nat}
    {e : Event} (ho : CreditOff o) (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) :
    (∃ par ok acq sc, e.kind = .wait (obj L g o) par ok acq sc) ∨
      (e.kind = .arrive (obj L g o) 0 1 true .cta ∧ h / L.block = g / L.block ∧
        8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  cases hu with
  | epiArr _ _ ho' | softArr _ _ _ ho' | ldAsync _ ho' => omega
  | ldArr _ _ ho' | ldCopy _ _ _ ho' => unfold LdTmaOff at ho'; omega
  | mmaCommit _ _ ho' => unfold MmaCommitOff at ho'; omega
  | epiPoll _ ok _ _ hk | corrPoll ok _ _ hk | softPoll _ ok _ _ _ hk | mmaPoll ok _ _ hk
  | ldPoll _ ok _ _ hk => exact .inl ⟨_, ok, true, .cta, hk⟩
  | corrArr hw _ hk => exact .inr ⟨hk, hc, hw⟩

/-- **A poll of a credit barrier** is a softmax lane's of the stage, with the parity of its
successful polls plus one. -/
theorem credit_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (st : Fin 2) {h k pc par : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .wait (obj L g (192 + 8 * st.val)) par ok acq sc⟩) :
    par % 2 = (okPolls (obj L g (192 + 8 * st.val)) ((X.tr h).take k) + 1) % 2 ∧ acq = true ∧
      h / L.block = g / L.block ∧ Prologue.warpIndex L h < 8 ∧
      Prologue.warpIndex L h / 4 = st.val := by
  obtain ⟨hc, hu⟩ := bar_use (o := 192 + 8 * st.val) hp hX hFw he rfl (fun _ h => by cases h)
  cases hu with
  | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
  | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
  | epiPoll _ _ _ ho | corrPoll _ _ ho => omega
  | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
  | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
  | softPoll a ok' hw ha ho hk =>
    have ha' : a = 192 := by omega
    subst ha'
    simp only [Kind.wait.injEq] at hk
    obtain ⟨-, rfl, -, hacq, -⟩ := hk
    refine ⟨?_, hacq, hc, hw, by omega⟩
    simp [softΔ]

theorem credit_init (st : Fin 2) :
    initOff ⟨24 + st.val, by omega⟩ = 192 + 8 * st.val ∧ initCnt ⟨24 + st.val, by omega⟩ = 128 := by
  fin_cases st <;> exact ⟨rfl, rfl⟩

/-- **Stage `st`'s credit barrier is a unit object** of the CTA's 128 correction lanes, polled with
offset 1. -/
theorem creditObj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (g : Nat) (st : Fin 2) :
    PTX.MbarRing.Unit.Obj X (obj L g (192 + 8 * st.val)) 128 (corrLane L (g / L.block)) 1 := by
  have ho : CreditOff (192 + 8 * st.val) := by unfold CreditOff; omega
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (obj L g (192 + 8 * st.val)))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g (192 + 8 * st.val)) c) =>
    credit_use hp hX hFw ho he hm hni
  obtain ⟨hloc, hcnt⟩ := credit_init st
  refine ⟨by decide, corrLane_inj L _, fun r hr => ?_, ?_, ?_, fun {h k pc par acq sc} he => ?_,
    le_refl 1⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | @arrive g' j pc tx c rel sc hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hk, hc, hw⟩
      · cases hk
      · simp only [Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hk
        obtain ⟨a, ha'⟩ := corrLane_of hp hc hw
        exact .arrive hid ⟨a, ha'⟩ he ha
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | increment hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | arriveOn hid he hm hn ha =>
      rcases hU he hm.symm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | bulk hid he hc hn ha =>
      rcases hU he hc (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | commit hid he ht ha =>
      rcases hU he ⟨_, ht⟩ (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases hU he ⟨_, htg, hm⟩ (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
  · rw [← hloc, ← hcnt]
    exact obj_initFirst hp hX hFw g _
  · exact AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _
  · exact (credit_poll hp hX hFw st he).1

end
end PTX.Kernels.TmlFa4Fwd.Proof
