-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvTrace
public import Kernels.InklingRelDecode.Proof.Interface.RdDPred
public import Kernels.InklingRelDecode.Proof.Interface.RdShapeSm
public import Kernels.InklingRelDecode.Proof.Interface.RsMmaBack

@[expose] public section

/-!
# The softmax region's states before and after the S-tile load

The S tile's load (`ldS`) is entered from the broadcast of the warp index (`shfl4`), which is
entered from the successful poll of `s_ready` (`waitS`), all in one iteration; the load is followed
by `waitLd`. These are the one-step inversions of `Sm.next` and the thread-level facts the
S-load's protocol statements need:

* `ldS_back`: the state at `ldS` at event `k` is two events after the state at `waitS` of the same
  iteration, whose event is a successful poll;
* `shfl4_event`: the event at the state `shfl4` is a shuffle;
* `ldS_succ`: the state after `ldS` is `waitLd` of the same iteration, when the thread has a later
  event that is not undefined behaviour (where a loaded word is not four bytes the machine is dead
  after the load, and every later event is undefined behaviour).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Sv

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The state before `ldS` is `shfl4` of the same iteration. -/
theorem next_ldS {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d.site = .ldS) : d0.site = .shfl4 ∧ d.i = d0.i := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (have := afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := toBar20_site hn; simp_all)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at hs)

/-- The state before `shfl4` is `waitS` of the same iteration, at a successful poll. -/
theorem next_shfl4 {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d.site = .shfl4) :
    d0.site = .waitS ∧ d.i = d0.i ∧ ∃ l p a sc, e.kind = .wait l p true a sc := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (have := afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := toBar20_site hn; simp_all)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at hs)


/-- **Two events before the S load**: the state at `ldS` at event `k` is the state at `shfl4` one
event before and the state at `waitS` two events before, of the same iteration; the event two
before is a successful poll and the event before it is a shuffle. -/
theorem ldS_back (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hg : g < L.threads) {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .ldS) :
    ∃ (k2 : Nat) (d2 d1 : D) (e2 e1 : Event), k = k2 + 2 ∧ (X.tr g)[k2]? = some e2 ∧
      (X.tr g)[k2 + 1]? = some e1 ∧ St Q L X g k2 = some (some (.d (.sm d2))) ∧
      d2.site = .waitS ∧ d2.i = d.i ∧ (∃ l p a sc, e2.kind = .wait l p true a sc) ∧
      St Q L X g (k2 + 1) = some (some (.d (.sm d1))) ∧ d1.site = .shfl4 ∧
      ∃ pc recv ok, e1 = ⟨pc, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩ := by
  rcases pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
  · simp [SmEntry.d0] at hs
  obtain ⟨hs1, hi1⟩ := next_ldS hn1 hs
  rcases pred_sm (by omega) hσ1 with ⟨dt, rfl⟩ | ⟨k2, d2, e2, rfl, he2, hσ2, hn2⟩
  · simp [SmEntry.d0] at hs1
  obtain ⟨hs2, hi2, hw⟩ := next_shfl4 hn2 hs1
  have hge1 : X.get (g, k2 + 1) = some e1 := he1
  obtain ⟨u, hF⟩ := fired_cont hX hf hg hge1 hσ1 (by simp [ExitState])
  obtain ⟨recv, ok, hev⟩ := Sm.shape_shfl4 (fired_sm hF) hs1
  exact ⟨k2, d2, d1, e2, e1, rfl, he2, he1, hσ2, hs2, by omega, hw, hσ1, hs1, _, recv, ok, hev⟩

/-- A thread whose last event is its exit has, after any event other than the exit, a later event
that is not undefined behaviour (the exit). -/
theorem later_of_exit {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hne : ∀ pc, e ≠ ⟨pc, .exit⟩) (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    ∃ j pc kd, k < j ∧ X.get (g, j) = some ⟨pc, kd⟩ ∧ ∀ f, kd ≠ .ub f := by
  obtain ⟨pc, hl⟩ := hex
  have hk : k < (X.tr g).length := len_of_get he
  have hlast : (X.tr g)[(X.tr g).length - 1]? = some ⟨pc, .exit⟩ := by
    rw [List.getLast?_eq_getElem?] at hl
    exact hl
  refine ⟨(X.tr g).length - 1, pc, .exit, ?_, hlast, fun f h => by cases h⟩
  by_contra hc
  have heq : k = (X.tr g).length - 1 := by omega
  have he' : (X.tr g)[k]? = some e := he
  rw [heq, hlast] at he'
  exact hne pc (Option.some.inj he').symm

/-- **The state after the S load** is `waitLd` of the same iteration, when the thread has a later
event that is not undefined behaviour. -/
theorem ldS_succ (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hg : g < L.threads) {k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .ldS)
    (hlater : ∃ j pc kd, k < j ∧ X.get (g, j) = some ⟨pc, kd⟩ ∧ ∀ f, kd ≠ .ub f) :
    ∃ d' : D, St Q L X g (k + 1) = some (some (.d (.sm d'))) ∧ d'.site = .waitLd ∧
      d'.i = d.i := by
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨vals, hl, hev⟩ := Sm.shape_ldS (fired_sm hF) hs
  have hst : St Q L X g (k + 1) = (threadCode L g Q).next (.d (.sm d)) e := by
    have : Frame.stateAt (code L Q) X g k = some (some (.d (.sm d))) := hσ
    show Frame.stateAt (code L Q) X g (k + 1) = _
    rw [Frame.stateAt_succ he', this]
    rfl
  have hnt := hf.tracked g (k + 1) hg
  have hnt' : St Q L X g (k + 1) ≠ some none := hnt
  rw [hst, next_d] at hnt'
  have hleave : ¬ DComp.leaves L g d e := by
    unfold DComp.leaves
    rw [hs]
    exact not_false
  have hsm : DComp.next L g Q (.sm d) e = (Sm.next L g d e).map (Option.map DComp.St.sm) := by
    show DComp.smNext L g d e = _
    unfold DComp.smNext
    simp only [hleave, ↓reduceIte]
  rw [hsm] at hnt'
  by_cases hb : ∀ x ∈ vals, x.bytes = 4
  · have hn := Sm.ld_next (L := L) (g := g) hs hl hb (a := Sm.tileAddr L g d)
      (sh := .s16x32bx2 64)
    refine ⟨{ d with site := .waitLd, sv := Sm.svOf vals hb }, ?_, rfl, rfl⟩
    rw [hst, next_d, hsm, hev, hn]
    rfl
  · exfalso
    obtain ⟨j, pcj, kd, hkj, hej, hub⟩ := hlater
    have hnone : St Q L X g (k + 1) = none := by
      have hh : ¬ (vals.length = 64 ∧ ∀ x ∈ vals, x.bytes = 4) := fun h => hb h.2
      rw [hst, next_d, hsm, hev]
      simp [Sm.next, hs, hh]
    have hj : St Q L X g j = none := Frame.stateAt_none_mono hnone (by omega)
    rcases Frame.fired hf.sound hX hej with ⟨σ, o, hσj, -⟩ | ⟨-, pc', f, he'⟩
    · have hj' : Frame.stateAt (fun g => threadCode L g Q) X g j = none := hj
      rw [hj'] at hσj
      cases hσj
    · simp only [Event.mk.injEq] at he'
      exact hub f he'.2


/-- The sites between the poll of `o_done` and the rescale load: after the poll succeeded, the
row sum's exchanges, the shared word, the test and the load (inclusive). -/
def PreLdO (s : Sm.Site) : Prop :=
  s = .bar22 ∨ s = .shfl7 ∨ s = .shfl8 ∨ s = .shfl9 ∨ s = .shfl10 ∨ s = .store10 ∨
    s = .bar23 ∨ s = .ldL ∨ s = .shfl11 ∨ s = .shfl12 ∨ s = .ldO

/-- One step into the window between the poll and the rescale load: from the successful poll, or
from a state of the window, in the same iteration. -/
theorem next_preLdO {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : PreLdO d.site) :
    d.i = d0.i ∧ ((d0.site = .waitO ∧ ∃ l p a sc, e.kind = .wait l p true a sc) ∨
      PreLdO d0.site) := by
  unfold PreLdO at hs
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [PreLdO]; done)
    | (have := afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := toBar20_site hn; simp_all)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at hs)

/-- **The window before the rescale load**: a softmax state at a site of the window has, at an
earlier event, the state at `waitO` of the same iteration with a successful poll, and every state
after it up to the state is at a site of the window. -/
theorem preLdO_back :
    ∀ (k : Nat), k ≤ (X.tr g).length → ∀ {d : D},
      St Q L X g k = some (some (.d (.sm d))) → PreLdO d.site →
      ∃ (kp : Nat) (dp : D) (ep : Event), kp < k ∧ (X.tr g)[kp]? = some ep ∧
        St Q L X g kp = some (some (.d (.sm dp))) ∧ dp.site = .waitO ∧ dp.i = d.i ∧
        (∃ l p a sc, ep.kind = .wait l p true a sc) ∧
        ∀ j, kp < j → j ≤ k → ∃ dj : D, St Q L X g j = some (some (.d (.sm dj))) ∧
          PreLdO dj.site := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d hσ hs
    rcases pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · exfalso
      simp [SmEntry.d0, PreLdO] at hs
    · obtain ⟨hi, hc⟩ := next_preLdO hn hs
      rcases hc with ⟨hw, hpl⟩ | hp0
      · refine ⟨k0, d0, e, by omega, he, hσ0, hw, by omega, hpl, fun j hj1 hj2 => ?_⟩
        have : j = k0 + 1 := by omega
        rw [this]
        exact ⟨d, hσ, hs⟩
      · obtain ⟨kp, dp, ep, hkp, hep, hσp, hwp, hip, hpl, hch⟩ :=
          ih k0 (by omega) (by omega) hσ0 hp0
        refine ⟨kp, dp, ep, by omega, hep, hσp, hwp, by omega, hpl, fun j hj1 hj2 => ?_⟩
        by_cases hjk : j = k0 + 1
        · exact ⟨d, by rw [hjk]; exact hσ, hs⟩
        · exact hch j hj1 (by omega)


/-- **The state after the rescale load** is `waitLdO` of the same iteration. -/
theorem ldO_succ (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hg : g < L.threads) {k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .ldO) :
    ∃ d' : D, St Q L X g (k + 1) = some (some (.d (.sm d'))) ∧ d'.site = .waitLdO ∧
      d'.i = d.i := by
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨vals, hl, hev⟩ := Sm.shape_ldO (fired_sm hF) hs
  have hst : St Q L X g (k + 1) = (threadCode L g Q).next (.d (.sm d)) e := by
    have : Frame.stateAt (code L Q) X g k = some (some (.d (.sm d))) := hσ
    show Frame.stateAt (code L Q) X g (k + 1) = _
    rw [Frame.stateAt_succ he', this]
    rfl
  have hnt := hf.tracked g (k + 1) hg
  have hnt' : St Q L X g (k + 1) ≠ some none := hnt
  rw [hst, next_d] at hnt'
  have hleave : ¬ DComp.leaves L g d e := by
    unfold DComp.leaves
    rw [hs]
    exact not_false
  have hsm : DComp.next L g Q (.sm d) e = (Sm.next L g d e).map (Option.map DComp.St.sm) := by
    show DComp.smNext L g d e = _
    unfold DComp.smNext
    simp only [hleave, ↓reduceIte]
  rw [hsm] at hnt'
  refine ⟨{ d with site := .waitLdO, stg := { d.stg with ow := Sm.owOf vals } }, ?_, rfl, rfl⟩
  rw [hst, next_d, hsm, hev]
  simp only [Sm.next, hs]
  rfl

/-- **The wait after the rescale load**: in a complete execution the event after the rescale
load is the thread's `tcgen05.wait::ld`. -/
theorem ldO_wait (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X)
    (hc : Complete L X) (hg : g < L.threads) {k : Nat} {d : D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .ldO) : ∃ pcw, X.get (g, k + 1) = some ⟨pcw, .tc .waitLd⟩ := by
  obtain ⟨d', hσ', hs', -⟩ := ldO_succ hX hf hg he hσ hs
  have hk := lt_length_of_complete hX hf hc hg hσ'
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, k + 1) = some e' := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he' hσ' (by simp [ExitState])
  have hblk : L.block % 32 = 0 := by rw [hpre.block]
  have := Sm.shape_waitLdO hblk (fired_sm hF) hs'
  exact ⟨_, by rw [he', this]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
