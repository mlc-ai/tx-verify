-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeOwn
public import Kernels.InklingRelDecode.Proof.Protocol.SOEpi
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmRun
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmEvents
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0

@[expose] public section

/-!
# A default-partition thread exits after a successful poll of `o_final`

After the second kernel fix the epilogue polls `o_final` on every path, also when `num_iters < 1`
(`Epi.D.start`, `Epi.D.startSk`: both enter at the `wait` site). So the poll is a measure of the
thread's abstract state: `exitP s` is `SO.epiPolled d` at an epilogue state `d` (none at the
`wait` site, one at every later site, the exit site included) and 0 at every other state. A step
raises it only at a successful poll at the `wait` site, and the only way into the epilogue is the
softmax region's exit, which enters at the `wait` site. Hence:

* `exit_poll`: a default-partition thread whose trace has an exit event has, before it, a
  successful acquire poll of `o_final` of its CTA (`wait (oFinal L c) p true true sc`).

No premise but `Pre` and the thread facts (`ThreadFacts`, `Epi.Means` through `reach`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Life
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO
  (epiPolled epi_next_polled ends_not_okW loc_oFinal)
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The successful `o_final` polls a thread's state has behind it. -/
def exitP : TSt → Nat
  | .d (.epi d) => epiPolled d
  | _ => 0

/-- A step from a state that is no epilogue state leaves an epilogue state only at its first
site, and no other state has polled. -/
theorem exitP_next_other {g : Nat} {s s' : TSt} {e : Event}
    (h : (threadCode L g Q).next s e = some (some s')) (hs : ∀ d, s ≠ .d (.epi d)) :
    exitP s' = 0 := by
  cases s with
  | w s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some s') from h)
    rfl
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from h)
    cases s with
    | dstart d =>
      simp only [DComp.next, DComp.dstartNext] at ha
      obtain ⟨a', ha', rfl⟩ := map_map_eq_some_some ha
      by_cases hq : a'.site = DStart.Site.toProA <;> simp only [hq, ↓reduceIte] <;> rfl
    | pro d =>
      simp only [DComp.next, DComp.proNext] at ha
      split at ha
      · split at ha
        · simp only [Option.some.injEq] at ha
          subst ha
          rfl
        · simp at ha
      · obtain ⟨a', ha', rfl⟩ := map_map_eq_some_some ha
        rfl
    | sm d =>
      simp only [DComp.next, DComp.smNext] at ha
      split at ha
      · simp only [DComp.exitNext] at ha
        split at ha
        · simp only [Option.some.injEq] at ha
          subst ha
          by_cases hq : (DComp.exitIn L g d).skip = true <;> simp only [hq, ↓reduceIte] <;> rfl
        · simp at ha
      · obtain ⟨a', ha', rfl⟩ := map_map_eq_some_some ha
        rfl
    | epi d => exact absurd rfl (hs d)

/-- **The poll measure along a thread**: at every state before an event, if the state's epilogue
has polled, an earlier event of the thread is a successful acquire poll of `o_final`. -/
theorem exitP_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} (hg : g < L.threads) :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) → 1 ≤ exitP s →
      ∃ j < k, ∃ pc p sc,
        X.get (g, j) = some ⟨pc, .wait (oFinal L (g / L.block)) p true true sc⟩ := by
  intro k
  induction k with
  | zero =>
    intro s _ hs h1
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    exfalso
    have h0 : exitP (threadCode L g Q).init = 0 := by
      show exitP (if g % L.block < 128 then .d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init) = 0
      split_ifs <;> rfl
    omega
  | succ k ih =>
    intro s' hk hs' h1
    have hs'' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L g Q).next s e = some (some s') := hs''
        have hget : X.get (g, k) = some e := he
        by_cases hep : ∃ d, s = .d (.epi d)
        · obtain ⟨d, rfl⟩ := hep
          obtain ⟨t, ins, o', hat, hinv, hc, hfire⟩ := Frame.fired_site hf.sound hX hget hσ
          have hI : Epi.Inv d := hinv.2.1
          have hm : Epi.Means Q L g d.pr := (hf.reach hg hσ).2
          obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q (.epi d) e).map
            (Option.map TSt.d) = some (some s') from hn)
          simp only [DComp.next] at ha
          obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some ha
          have hpol := epi_next_polled hI hd'
          by_cases hw : d.site = .wait ∧ okW e = true
          · -- the poll
            have hevent : ∃ pc p sc,
                e = ⟨pc, .wait (oFinal L (g / L.block)) p true true sc⟩ := by
              obtain ⟨o'', hF⟩ := (Frame.trace hf.sound hX hg).fired_at he hσ
              cases o'' with
              | none =>
                obtain ⟨t', -, hf'⟩ := hF
                have hend := fires_none_ends hf'
                have := ends_not_okW hend
                rw [this] at hw
                exact absurd hw.2 (by simp)
              | some u =>
                obtain ⟨ok, hev⟩ := Epi.shape_wait_oFinal (ProA.sharedOk_of_pre hpre).2 hm
                  (fired_epi hF) hw.1
                rw [loc_oFinal] at hev
                have hok := hw.2
                rw [hev] at hok
                simp only [okW] at hok
                subst hok
                exact ⟨_, _, _, hev⟩
            obtain ⟨pc, p, sc, hev⟩ := hevent
            refine ⟨k, Nat.lt_succ_self k, pc, p, sc, ?_⟩
            have hok : okW e = true := hw.2
            have : X.get (g, k) = some e := hget
            rw [hev] at this
            have hev' : e = ⟨pc, .wait (oFinal L (g / L.block)) p true true sc⟩ := hev
            rw [← hev']
            exact hget
          · have hd0 : epiPolled d' = epiPolled d := by simpa [hw] using hpol
            have h1' : 1 ≤ exitP (.d (.epi d)) := by
              simp only [exitP] at h1 ⊢
              omega
            obtain ⟨j, hj, hr⟩ := ih (.d (.epi d)) (by omega) hσ h1'
            exact ⟨j, by omega, hr⟩
        · have := exitP_next_other (g := g) hn (fun d h => hep ⟨d, h⟩)
          omega

/-- **A default-partition thread that exits polled `o_final` before**: the epilogue waits for
`o_final` on every path. -/
theorem exit_poll (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g kh pc : Nat} (he : X.get (g, kh) = some ⟨pc, .exit⟩)
    (hd : g % L.block < 128) :
    ∃ j < kh, ∃ pc' p sc,
      X.get (g, j) = some ⟨pc', .wait (oFinal L (g / L.block)) p true true sc⟩ := by
  have hg := Frame.lt_of_get hX he
  have hlen : kh ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  rcases exit_event_state hX hf.sound hf.tracked he with ⟨d, hσ, hs⟩ | ⟨x, hσ, hs⟩
  · refine exitP_inv hpre hX hf hg kh _ hlen hσ ?_
    simp only [exitP, epiPolled, hs]
    omega
  · exfalso
    have h := (cls_inv kh _ hlen hσ).mpr hd
    simp [TSt.isD] at h

end
end PTX.Kernels.InklingRelDecode.Proof.Life
