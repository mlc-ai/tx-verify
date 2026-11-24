-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Lemmas.Protocol.UnitHandoff
public import Lemmas.Protocol.UnitReachBlocker
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Lemmas.Protocol.ObjectSource
import Lemmas.Protocol.UnitItems
import Lemmas.Protocol.UnitRing
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The free barriers

The output warp's free barrier of stage `st` (shared offset `224 + 8 st`, count 32) is arrived on
once by each of the output warp's 32 lanes (`outLane`) and polled by the correction lanes, whose
first poll passes on the fresh barrier (`freeObj`: a unit object polled with offset 1). An arrival
is its lane's only one, so it needs no earlier poll (`freeReach`), and a correction lane's second
poll synchronizes with every output lane's arrival (`freeHandoff`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The output warp's lanes of CTA `c`: lanes 416 to 447. -/
def outLane (L : Launch) (c : Nat) (a : Fin 32) : Nat := c * L.block + 416 + a.val

theorem outLane_inj (L : Launch) (c : Nat) : Function.Injective (outLane L c) := by
  intro a b h
  simp only [outLane] at h
  exact Fin.ext (by omega)

theorem outLane_of (hp : Pre p L m) {h c : Nat} (hc : h / L.block = c)
    (hw : Prologue.warpIndex L h = 13) : ∃ a, h = outLane L c a := by
  have hb := hp.block
  have hm := Nat.div_add_mod h L.block
  rw [hc] at hm
  simp only [Prologue.warpIndex, hb] at hw hm
  refine ⟨⟨h % 512 - 416, by omega⟩, ?_⟩
  simp only [outLane, hb]
  omega

theorem outLane_cta (hp : Pre p L m) (c : Nat) (a : Fin 32) : outLane L c a / L.block = c := by
  have hb := hp.block
  have ha := a.isLt
  unfold outLane
  rw [hb]
  omega

/-- The correction lanes of lane `g`'s CTA. -/
def CorrIn (L : Launch) (g h : Nat) : Prop :=
  h < L.threads ∧ h / L.block = g / L.block ∧ 8 ≤ Prologue.warpIndex L h ∧
    Prologue.warpIndex L h ≤ 11

theorem free_init (st : Fin 2) : initOff ⟨28 + st.val, by omega⟩ = 224 + 8 * st.val ∧
    initCnt ⟨28 + st.val, by omega⟩ = 32 := by
  fin_cases st <;> exact ⟨rfl, rfl⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Who names a free barrier**: a correction lane's poll, or an output lane's only arrival. -/
theorem free_use (st : Fin 2) {h k : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hm : MbarOf e (obj L g (224 + 8 * st.val)))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g (224 + 8 * st.val)) c) :
    h / L.block = g / L.block ∧
      ((∃ ok, e.kind = .wait (obj L g (224 + 8 * st.val))
          ((okPolls (obj L g (224 + 8 * st.val)) ((X.tr h).take k) + 1) % 2) ok true .cta) ∨
        e.kind = .arrive (obj L g (224 + 8 * st.val)) 0 1 true .cta ∧
          Prologue.warpIndex L h = 13 ∧
          arrivals (obj L g (224 + 8 * st.val)) ((X.tr h).take k) = 0) := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  refine ⟨hc, ?_⟩
  cases hu with
  | epiArr st' hw _ hk h0 => exact .inr ⟨hk, hw, h0⟩
  | corrPoll ok _ _ hk =>
    have hΔ : corrΔ (224 + 8 * st.val) = 1 := by unfold corrΔ; split <;> omega
    rw [hΔ] at hk
    exact .inl ⟨ok, hk⟩
  | epiPoll _ _ _ ho | corrArr _ ho | softArr _ _ _ ho | softPoll _ _ _ _ ho
  | ldAsync _ ho => omega
  | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
  | mmaCommit _ _ ho => unfold MmaCommitOff at ho; omega
  | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
  | ldArr _ _ ho | ldCopy _ _ _ ho => unfold LdTmaOff at ho; omega

/-- **The free barrier of stage `st` is a unit object** of the CTA's 32 output lanes. -/
theorem freeObj (g : Nat) (st : Fin 2) :
    Unit.Obj X (obj L g (224 + 8 * st.val)) 32 (outLane L (g / L.block)) 1 := by
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (obj L g (224 + 8 * st.val)))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g (224 + 8 * st.val)) c) =>
    free_use hp hX hFw st he hm hni
  obtain ⟨hloc, hcnt⟩ := free_init st
  refine ⟨by decide, outLane_inj L _, fun r hr => ?_, ?_, ?_,
    fun {h k pc par acq sc} he => ?_, le_refl 1⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | @arrive g' j pc tx c rel sc hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨hc, ⟨_, hk⟩ | ⟨hk, hw, -⟩⟩
      · cases hk
      · simp only [Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hk
        obtain ⟨a, ha'⟩ := outLane_of hp hc hw
        exact .arrive hid ⟨a, ha'⟩ he ha
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | increment hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases hU he hm (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | arriveOn hid he hm hn ha =>
      rcases hU he hm.symm (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | bulk hid he hc hn ha =>
      rcases hU he hc (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | commit hid he ht ha =>
      rcases hU he ⟨_, ht⟩ (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases hU he ⟨_, htg, hm⟩ (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
  · rw [← hloc, ← hcnt]
    exact obj_initFirst hp hX hFw g _
  · exact AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _
  · rcases hU he rfl (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -⟩ := hk
      omega
    · cases hk

/-- **The free barriers are not reused**: every arrival is its lane's first. -/
theorem freeReach (g : Nat) (st : Fin 2) (h : Nat) :
    Unit.Reach L kernel Assumptions.all X (obj L g (224 + 8 * st.val)) 32
      (outLane L (g / L.block)) 1 h := by
  intro x hx j hj
  exfalso
  obtain ⟨-, ⟨pc, sc, hget⟩, harr⟩ := (freeObj hp hX hFw g st).S_rec hx
  rcases free_use hp hX hFw st (h := outLane L (g / L.block) x.1) hget rfl
    (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨-, -, h0⟩⟩
  · cases hk
  · have h1 := harr.symm.trans h0
    omega

/-- **The free hand-off.** -/
theorem freeHandoff (g : Nat) (st : Fin 2) :
    UnitHandoff L X (obj L g (224 + 8 * st.val))
      (fun y => ∃ a, y = outLane L (g / L.block) a) (CorrIn L g) 1 := by
  refine (freeObj hp hX hFw g st).handoff hX (fun h _ => freeReach hp hX hFw g st h)
    (fun {h j pc par acq sc} hh he => ?_) (fun {a h i j pc pc' par acq sc sc'} hh ha he => ?_)
  · rcases free_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨hk, -⟩⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, -, -, ho, -⟩ := hk
      exact ho
    · cases hk
  · rcases free_use hp hX hFw st ha rfl (fun _ h => by cases h) with ⟨_, ⟨_, hk⟩ | ⟨hk, -⟩⟩
    · cases hk
    rcases free_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨_, ⟨_, hk'⟩ | ⟨hk', -⟩⟩
    swap; · cases hk'
    simp only [Kind.arrive.injEq] at hk
    simp only [Kind.wait.injEq] at hk'
    obtain ⟨-, -, -, -, rfl⟩ := hk
    obtain ⟨-, -, -, -, rfl⟩ := hk'
    have hc := (outLane_cta hp (g / L.block) a).trans hh.2.1.symm
    exact ⟨⟨Frame.lt_of_get hX ha, hh.1, hc⟩, hh.1, Frame.lt_of_get hX ha, hc.symm⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
