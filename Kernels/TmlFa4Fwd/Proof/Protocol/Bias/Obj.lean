-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
public import Lemmas.Protocol.TmaUnit
public import Lemmas.Protocol.UnitObject
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Lemmas.Protocol.ObjectSource
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias barriers

Stage `st`'s bias full barrier (shared offset `320 + 8 st`, count 1) is filled by the loader: an
expect-tx arrival and tensor copies (`biasObj`: `MbarRing.TmaUnitObject`), and polled by the stage's
softmax lanes with the parity of their earlier polls (`bias_poll`). Its empty barrier
(`336 + 8 st`, count 4) is arrived on by lane 0 of each of the stage's four softmax warps, after one
more full poll than its earlier arrivals (`biasFree_arr`), and polled by the loader
(`biasFreeHist`: the history of a unit object of those four lanes). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem bias_init (st : Fin 2) : initOff ⟨30 + st.val, by omega⟩ = 320 + 8 * st.val ∧
    initCnt ⟨30 + st.val, by omega⟩ = 1 := by
  fin_cases st <;> exact ⟨rfl, rfl⟩

theorem biasFree_init (st : Fin 2) : initOff ⟨32 + st.val, by omega⟩ = 336 + 8 * st.val ∧
    initCnt ⟨32 + st.val, by omega⟩ = 4 := by
  fin_cases st <;> exact ⟨rfl, rfl⟩

/-- Lane 0 of softmax warp `a + 4 st` of CTA `c`. -/
def biasLane (L : Launch) (c st : Nat) (a : Fin 4) : Nat := c * L.block + 32 * (4 * st + a.val)

theorem biasLane_inj (L : Launch) (c st : Nat) : Function.Injective (biasLane L c st) := by
  intro a b h
  simp only [biasLane] at h
  exact Fin.ext (by omega)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Who names a bias full barrier**: a softmax lane's poll of the stage, a loader lane's expect-tx
arrival, or a loader lane's tensor copy. -/
theorem bias_use (st : Fin 2) {h k : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hm : MbarOf e (obj L g (320 + 8 * st.val)))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g (320 + 8 * st.val)) c) :
    h / L.block = g / L.block ∧
      ((∃ ok, Prologue.warpIndex L h < 8 ∧ Prologue.warpIndex L h / 4 = st.val ∧
          e.kind = .wait (obj L g (320 + 8 * st.val))
            (okPolls (obj L g (320 + 8 * st.val)) ((X.tr h).take k) % 2) ok true .cta) ∨
        (LdLane L g h ∧ ∃ tx, e.kind = .arrive (obj L g (320 + 8 * st.val)) tx 1 true .cta) ∨
        LdLane L g h ∧ ∃ a sp, e.kind = .tensorIssue a sp ∧
          sp.mbar = obj L g (320 + 8 * st.val)) := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  refine ⟨hc, ?_⟩
  cases hu with
  | softPoll a ok hw ha ho hk =>
    have ha' : a = 320 := by omega
    subst ha'
    exact .inl ⟨ok, hw, by omega, by simpa [softΔ] using hk⟩
  | ldArr tx hw _ hk => exact .inr (.inl ⟨⟨hc, hw⟩, tx, hk⟩)
  | ldCopy a sp hw _ hk hb => exact .inr (.inr ⟨⟨hc, hw⟩, a, sp, hk, hb⟩)
  | epiPoll _ _ _ ho | epiArr _ _ ho | corrPoll _ _ ho | corrArr _ ho | softArr _ _ _ ho
  | ldAsync _ ho => omega
  | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
  | mmaCommit _ _ ho => unfold MmaCommitOff at ho; omega
  | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega

/-- **The bias full barrier is a one-CTA TMA unit object** of the CTA's loader lanes. -/
theorem biasObj (g : Nat) (st : Fin 2) :
    MbarRing.TmaUnitObject X (obj L g (320 + 8 * st.val)) (LdLane L g) := by
  obtain ⟨hloc, hcnt⟩ := bias_init st
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (obj L g (320 + 8 * st.val)))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g (320 + 8 * st.val)) c) =>
    (bias_use hp hX hFw st he hm hni).2
  have hinit : PairTmaRing.InitFirst X (obj L g (320 + 8 * st.val)) 1 := by
    rw [← hloc, ← hcnt]
    exact obj_initFirst hp hX hFw g _
  refine MbarRing.TmaUnitObject.of_issues hX hinit
    (fun i h => no_inval hp hX hFw i _ h)
    (fun h k pc tx c rel sc he => ?_) (fun ⟨h, k⟩ noinc ⟨pc, he⟩ => ?_)
    (fun ⟨h, k⟩ s ⟨pc, he⟩ hm => ?_) (fun ⟨h, k⟩ s rank ⟨pc, he⟩ hm => ?_)
    (fun ⟨h, k⟩ sp tg c ⟨pc, he⟩ hm => ?_)
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, hk⟩ | ⟨hl, tx', hk⟩ |
      ⟨_, _, _, hk, _⟩
    · cases hk
    · simp only [Kind.arrive.injEq] at hk
      obtain ⟨-, -, rfl, rfl, -⟩ := hk
      exact ⟨hl, rfl, rfl⟩
    · cases hk
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ |
      ⟨_, _, _, hk, _⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ |
      ⟨_, _, _, hk, _⟩ <;> cases hk
  · rcases hU he ⟨_, hm⟩ (fun _ h => by cases h) with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ |
      ⟨_, _, _, hk, _⟩ <;> cases hk
  · exact no_clc hp hX hFw h k pc sp tg he

/-- **Who names a bias empty barrier**: a loader lane's poll, or the unit release arrival of lane 0
of a softmax warp of the stage, after one more full poll than its earlier arrivals. -/
theorem biasFree_use (st : Fin 2) {h k : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hm : MbarOf e (obj L g (336 + 8 * st.val)))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g (336 + 8 * st.val)) c) :
    (LdLane L g h ∧ ∃ par ok, e.kind = .wait (obj L g (336 + 8 * st.val)) par ok true .cta) ∨
      e.kind = .arrive (obj L g (336 + 8 * st.val)) 0 1 true .cta ∧
        (∃ a, h = biasLane L (g / L.block) st.val a) ∧
        okPolls (obj L g (320 + 8 * st.val)) ((X.tr h).take k) =
          arrivals (obj L g (336 + 8 * st.val)) ((X.tr h).take k) + 1 := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  cases hu with
  | ldPoll par ok hw _ hk => exact .inl ⟨⟨hc, hw⟩, par, ok, hk⟩
  | softArr a hw ha ho hk =>
    have ha' : a = 336 := by omega
    subst ha'
    refine .inr ⟨hk, ?_⟩
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    have hso : ∀ b, sobj L h b = obj L g (b + 8 * st.val) := fun b => by
      rw [sobj, obj_cta hc]; congr 1; omega
    rw [← hso] at he
    obtain ⟨h1, h2⟩ := soft_b_arr hp hX hFw hw he
    rw [hso, hso] at h2
    refine ⟨⟨⟨Prologue.warpIndex L h % 4, by omega⟩, ?_⟩, h2⟩
    have hb := hp.block
    have hmod := Nat.div_add_mod h L.block
    rw [hc] at hmod
    simp only [Prologue.warpIndex, hb] at hw ho h1 hmod ⊢
    simp only [biasLane, hb]
    omega
  | softPoll _ _ _ _ ho | epiPoll _ _ _ ho | epiArr _ _ ho | corrPoll _ _ ho | corrArr _ ho
  | ldAsync _ ho => omega
  | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
  | mmaCommit _ _ ho => unfold MmaCommitOff at ho; omega
  | ldArr _ _ ho | ldCopy _ _ _ ho => unfold LdTmaOff at ho; omega

/-- **The bias empty barrier's history**: unit arrivals of the four lanes (the loader's parities are
not stated). -/
theorem biasFreeHist (g : Nat) (st : Fin 2) :
    MbarRing.Unit.History X (obj L g (336 + 8 * st.val)) 4 (biasLane L (g / L.block) st.val) := by
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (obj L g (336 + 8 * st.val)))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g (336 + 8 * st.val)) c) =>
    biasFree_use hp hX hFw st he hm hni
  obtain ⟨hloc, hcnt⟩ := biasFree_init st
  refine ⟨by decide, biasLane_inj L _ _, fun r hr => ?_, ?_, ?_⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | @arrive g' j pc tx c rel sc hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨-, _, _, hk⟩ | ⟨hk, ha', -⟩
      · cases hk
      · simp only [Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hk
        exact .arrive hid ha' he ha
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | increment hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨-, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases hU he hm (fun _ h => by cases h) with ⟨-, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | arriveOn hid he hm hn ha =>
      rcases hU he hm.symm (fun _ h => by cases h) with ⟨-, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | bulk hid he hc hn ha =>
      rcases hU he hc (fun _ h => by cases h) with ⟨-, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | commit hid he ht ha =>
      rcases hU he ⟨_, ht⟩ (fun _ h => by cases h) with ⟨-, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases hU he ⟨_, htg, hm⟩ (fun _ h => by cases h) with ⟨-, _, _, hk⟩ | ⟨hk, -⟩ <;> cases hk
  · rw [← hloc, ← hcnt]
    exact obj_initFirst hp hX hFw g _
  · exact AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
