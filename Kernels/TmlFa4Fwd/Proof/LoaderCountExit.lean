-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderExit
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private theorem eventfulWalkRun {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {vs : List Visit} (hw : Walk K A l g s es vs) :
    ∃ o, Run K A l g s es o := by
  induction hw with
  | stop => exact ⟨some _, .nil _⟩
  | tau h _ ih =>
    obtain ⟨_, hTail⟩ := ih
    cases hTail with
    | nil => exact ⟨some _, .nil _⟩
    | step hLocal he hRest => exact ⟨_, .step (.head h hLocal) he hRest⟩
    | last hLocal he => exact ⟨none, .last (.head h hLocal) he⟩
  | ev he _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r, .step .refl he hr⟩
  | last he => exact ⟨none, .last .refl he⟩

private theorem loaderExitWalk {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hAt : At s 1901 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hw : Walk kernel Assumptions.all l g s es vs) : es.countP Event.counts ≤ 1 := by
  obtain ⟨o, hr⟩ := eventfulWalkRun hw
  obtain ⟨u, hp, hn⟩ := loaderRoleExit warp hAt
  cases o with
  | none =>
    rw [loaderRoleExitSuffix warp hAt hr]
    decide
  | some v =>
    cases hr with
    | nil => simp
    | step ht he _ =>
      have hu := stop_unique ht hn.steps (stops_of_estep he) ⟨_, hn.stop⟩
      subst u
      obtain ⟨m, hm, hf⟩ := he
      rw [hn.stop] at hm
      obtain rfl := Out.ev.inj hm
      cases hf.2

private theorem loaderExitCutCode :
    ((kernel.code.drop 174).take (1901 - 174)).all
      (fun i => loaderPipelineCutOp 174 1901 9206 [2535, 1062] i.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

/-- The loader whole-program walk lies in its role up to the known dispatch to
the common return path. At most the return lies beyond the role's counted prefix. -/
theorem loaderWholeEventCount {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hs : At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP Event.counts ≤ loaderEventCount vs + 1 := by
  let F := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]
  have advance {t u : TState} {e : Option Event} {rest : List Event} {tail : List Visit}
      (hp : 174 ≤ t.pc ∧ t.pc ≤ 1901) (hR : RingShape t) (hF : Holds t.regs F)
      (hStep : WStep kernel Assumptions.all l g t e u)
      (hWalk : Walk kernel Assumptions.all l g t (e.toList ++ rest)
        (visit kernel l g t e :: tail))
      (ih : (174 ≤ u.pc ∧ u.pc ≤ 1901) → RingShape u → Holds u.regs F →
        rest.countP Event.counts ≤ loaderEventCount tail + 1) :
      (e.toList ++ rest).countP Event.counts ≤
        loaderEventCount (visit kernel l g t e :: tail) + 1 := by
    by_cases hEnd : t.pc = 1901
    · by_cases hf : t.fault = none
      · have ht : At t 1901 F := pipelineAtCut hEnd hR hF hf ⟨_, Flow.code_1901, rfl⟩
        exact (loaderExitWalk warp ht hWalk).trans (by omega)
      · rcases hStep with ⟨_, ht⟩ | ⟨_, _, he⟩ <;>
          cases hf' : t.fault
        · exact (hf hf').elim
        · simp [Tau, out, hf'] at ht
        · exact (hf hf').elim
        · obtain ⟨tmp, hout, hf⟩ := he
          simp only [out, hf', Out.ev.injEq] at hout
          subst tmp
          cases hf.2
    · have ht : t.pc < 1901 := by omega
      obtain ⟨hl, hu | hFar, hShape, hHold⟩ := pipelineCutStep
        (lower := 174) (cut := 1901) (branch := 9206) (F := F) (by decide) (by decide)
        ⟨hp.1, ht⟩ loaderExitCutCode hStep hR hF
      · have hh := ih ⟨hl, hu⟩ hShape hHold
        rw [eventCountCons ⟨hp.1, by omega⟩, List.countP_append]
        cases e with
        | none => simpa using hh
        | some e =>
          simp only [Option.toList, List.countP_cons, List.countP_nil, Nat.zero_add,
            Option.map_some, Option.getD_some]
          omega
      · exfalso
        have hf : u.pc ≤ 9206 := by
          rcases hStep with ⟨_, htau⟩ | ⟨ev, _, he⟩
          · have htau' : Tau kernel [] l g t u := by
              unfold Tau at htau ⊢
              rwa [← loaderOutCore hp.1 (by omega)]
            obtain ⟨ins, hc⟩ := tau_core_has_code htau'
            have hStepRange : ((kernel.code.drop 174).take (1901 - 174)).all
                (fun i => match i.op with
                  | .bra target _ => target ≤ 9206
                  | .brx .. => false
                  | _ => true) = true := by
              set_option maxRecDepth 100000 in decide +kernel
            have hGet : ((kernel.code.drop 174).take (1901 - 174))[t.pc - 174]? =
                some ins := by
              rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
                Nat.add_sub_of_le hp.1]
              exact hc
            have hOk := List.all_eq_true.mp hStepRange ins (List.mem_of_getElem? hGet)
            rcases tau_core_frame hc htau' with rfl | hFrame
            · exact show t.pc + 1 ≤ 9206 by omega
            · have hn := hFrame.pc
              cases hOp : ins.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hn
              case bra target uni =>
                rw [hn]
                exact of_decide_eq_true (by simpa only [hOp] using hOk)
              case brx => simp [hOp] at hOk
              all_goals omega
          · have he' : EStep kernel [] l g t ev (some u) := by
              obtain ⟨tmp, ho, hf⟩ := he
              exact ⟨tmp, by rwa [← loaderOutCore hp.1 (by omega)], hf⟩
            rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with he | he <;> omega
        omega
  have hP : 174 ≤ s.pc ∧ s.pc ≤ 1901 := by rw [hs.1]; decide
  have hR := ringShapeOfAt hs
  have hF : Holds s.regs F := hs.2.2.2.2
  clear hs
  induction hw with
  | stop => exact Nat.zero_le _
  | tau ht hw ih => exact advance hP hR hF (.inl ⟨rfl, ht⟩) (.tau ht hw) ih
  | ev he hw ih => exact advance hP hR hF (.inr ⟨_, rfl, he⟩) (.ev he hw) ih
  | last => exact (List.countP_le_length ..).trans (by simp)

end
end PTX.Kernels.TmlFa4Fwd.Loader
