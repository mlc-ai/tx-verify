-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcEffects
public import Mathlib.Tactic.NormNum

namespace PTX.Tests.ClcEffects
open PTX.Clc
noncomputable section

private def L : Launch := { grid := 8, block := 128, clusterSize := ⟨2, by decide⟩, params :=
                            fun _ => none }
private def spec : Clc.Spec := ⟨⟨.shared, 2, 32⟩, ⟨.shared, 2, 64⟩, true⟩
private def response : ClcResponse := responseOf L (256, 7) (some 3)
private def state : Clc.State := {
  owner := Function.update initial.owner 3 (some (.canceled (requestId (256, 7))))
  response := Function.update initial.response (requestId (256, 7)) (some (some 3))
}
private theorem oneDim : L.OneDim := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
private theorem gridValid : L.clusterGridValid := Launch.oneDimLaunch_clusterGridValid
  ⟨oneDim, by decide⟩
private theorem validTask3 : ValidTask L 3 := ⟨gridValid, by decide⟩
private theorem arbitration : ArbitrationOk L state := by
  exact .single (.success initial (requestId (256, 7)) 3 validTask3 rfl rfl)
private def failedState : Clc.State := {
  initial with response := Function.update initial.response (requestId (256, 7)) (some none)
}
private theorem failedArbitration : ArbitrationOk L failedState :=
  .single (.failure initial (requestId (256, 7)) rfl)

private def issued : Clc.Effects := {}
private def resolved : Clc.Effects := { resolved := some response }
private def firstDone : Clc.Effects := { resolved := some response, written := {2}, notified :=
                                         {2} }
private def bothDone : Clc.Effects := { resolved := some response, written := {2, 3}, notified :=
                                        {2, 3} }

example : Target L (256, 7) spec 2 := ⟨gridValid, by decide⟩
example : Target L (256, 7) spec 3 := ⟨gridValid, by decide⟩
example : ¬ Target L (256, 7) spec 4 := by
  rintro ⟨-, -, -, -, -, -, -, h8⟩
  exact absurd h8 (by decide)
example : ¬ Target L (256, 7) { spec with multicast := false } 3 := by
  rintro ⟨-, -, -, -, -, -, -, h8⟩
  exact absurd h8 (by decide)

-- Issue and resolution alone have not performed a memory write or a notification.
example : 2 ∉ issued.written := by simp [issued]
example : 2 ∉ resolved.written := by simp [resolved]
example : 2 ∉ resolved.notified := by simp [resolved]

-- CTA 2's completion neither completes nor publishes CTA 3's response.
example : Completion spec firstDone 2 ⟨.shared, 2, 64⟩ 16 := by
  simp [Completion, firstDone, spec]
example : ¬ Completion spec firstDone 3 ⟨.shared, 3, 64⟩ 16 := by
  simp [Completion, firstDone]
example : 3 ∉ firstDone.notified := by simp [firstDone]

example : EffectsOk L (256, 7) spec state firstDone := by
  refine ⟨arbitration, ?_, ?_, ?_⟩
  · intro r hr
    have he : r = response := by simpa [firstDone] using hr.symm
    subst r
    exact ⟨some 3, by simp [state], rfl⟩
  · intro c hc
    have he : c = 2 := by simpa [firstDone] using hc
    subst c
    exact ⟨⟨gridValid, by decide⟩, rfl⟩
  · intro c hc; exact hc

-- Both target writes have one payload, while each target has its own 16-byte notification.
example : Completion spec bothDone 3 ⟨.shared, 3, 64⟩ 16 := by simp [Completion, bothDone, spec]
example : ¬ Completion spec bothDone 3 ⟨.shared, 2, 64⟩ 16 := by simp [Completion, bothDone, spec]

-- Fabricating a notification before its target write fails the object-independent rule.
example : ¬ EffectsOk L (256, 7) spec state { resolved := some response, notified := {2} } := by
  intro h
  have := h.notified 2 (by simp)
  simp at this

-- Failure responses follow exactly the same write/notification protocol.
example : EffectsOk L (256, 7) spec failedState
    { resolved := some (responseOf L (256, 7) none), written := {2}, notified := {2} } := by
  refine ⟨failedArbitration, ?_, ?_, ?_⟩
  · intro r hr
    cases hr
    exact ⟨none, by simp [failedState], rfl⟩
  · intro c hc
    have he : c = 2 := by simpa using hc
    subst c
    exact ⟨⟨gridValid, by decide⟩, rfl⟩
  · intro c hc; exact hc

-- A response naming another task cannot be substituted for this request's result.
example : ¬ Result L (256, 7) state (responseOf L (256, 7) (some 2)) := by
  rintro ⟨task, ht, hr⟩
  have he : task = some 3 := by simpa [state] using ht.symm
  subst task
  have hx := congrArg ClcResponse.firstCta hr
  rw [responseOf_oneDim oneDim, responseOf_oneDim oneDim] at hx
  norm_num [L] at hx

end
end PTX.Tests.ClcEffects
