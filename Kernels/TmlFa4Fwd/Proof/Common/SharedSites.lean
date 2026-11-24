-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.Progress.PollsOn
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.ControlHandoff

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow
noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

/-- Startup and the roles whose local continuations have strict site proofs. -/
def strictSite (d : (thread p L g).D) : Bool :=
  match d.1 with
  | .inr ⟨.softmax, _⟩ | .inr ⟨.correction, _⟩ => false
  | _ => true

private abbrev restrictedFrag (p : Params) (L : Launch) (g : Nat) (i : Role) :
    Code kernel Assumptions.all L g :=
  { frag p L g i with next := match i with
    | .softmax | .correction => fun _ _ => some none
    | _ => (frag p L g i).next }

private abbrev restricted (p : Params) (L : Launch) (g : Nat) :=
  (Code.glue (Startup.code p L g) (restrictedFrag p L g) (exit L g)).counted (cls L g)

private theorem restricted_sound {m} (hp : Pre p L m) (hg : g < L.threads) :
    (restricted p L g).Sound := by
  apply Code.counted_sound
  refine Code.glue_sound (start hp) (startup_steps hp hg) ?_ ?_
  swap
  · intro s i t hx hat hi
    exact handoffU hp hg s i t hx hat hi
  intro i d
  cases i with
  | mma => exact fragD_steps hp hg .mma d
  | epilogue => exact fragD_steps hp hg .epilogue d
  | loader b => exact fragD_steps hp hg (.loader b) d
  | stub r => exact fragD_steps hp hg (.stub r) d
  | softmax => exact ⟨(frag_stepsU hp hg .softmax d).site, fun _ _ _ _ _ => .inl (.inl rfl)⟩
  | correction => exact ⟨(frag_stepsU hp hg .correction d).site, fun _ _ _ _ _ => .inl (.inl rfl)⟩

private def project (s : Option (Option (thread p L g).D)) := s.join.filter strictSite

private theorem advance (e : Event) (s : Option (Option (thread p L g).D)) (cut : Bool) :
    project (s.bind fun d => if cut then (restricted p L g).toMachine.next d e
      else (thread p L g).toMachine.next d e) =
      (project s).bind (fun d => project ((thread p L g).next d e)) := by
  rcases s with _ | _ | ⟨s,n⟩
  · cases cut <;> rfl
  · cases cut <;> rfl
  rcases s with s | ⟨i,d⟩
  · cases cut <;> rfl
  cases i with
  | correction | softmax =>
    cases cut <;> change project _ = none
    all_goals first
      | rfl
      | change project ((((frag p L g _).next d e).map _).map _) = none
        rcases (frag p L g _).next d e with _ | _ | d' <;> rfl
  | _ => cases cut <;> rfl

private theorem agreement (X : Execution) (k : Nat) :
    project (Frame.stateAt (thread p L) X g k) =
      project (Frame.stateAt (restricted p L) X g k) := by
  induction k with
  | zero => rw [Frame.stateAt_zero, Frame.stateAt_zero]; rfl
  | succ k ih =>
    by_cases h : k < (X.tr g).length
    · have he := List.getElem?_eq_getElem h
      rw [Frame.stateAt_succ he, Frame.stateAt_succ he]
      exact (advance _ _ false).trans ((congrArg (·.bind (fun d =>
        project ((thread p L g).next d (X.tr g)[k]))) ih).trans (advance _ _ true).symm)
    · have hk : (X.tr g).length ≤ k := by omega
      rw [Frame.stateAt_of_le (Nat.le_succ_of_le hk), Frame.stateAt_of_le (Nat.le_succ_of_le hk)]
      simpa only [Frame.stateAt_of_le hk] using ih

private theorem recover {X : Execution} {k d}
    (h : Frame.stateAt (thread p L) X g k = some (some d)) (hs : strictSite d = true) :
    Frame.stateAt (restricted p L) X g k = some (some d) := by
  have ha := agreement (p := p) (L := L) (g := g) X k
  rw [h] at ha
  rcases hd : Frame.stateAt (restricted p L) X g k with _ | _ | d' <;> rw [hd] at ha
  all_goals simp [project, hs, Option.filter] at ha
  rw [ha.2]

variable {m : Mem0} {X : Execution} {k : Nat} {d : (thread p L g).D}

theorem strict_fired (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {e : Event} (he : X.get (g,k) = some e)
    (h : Frame.stateAt (thread p L) X g k = some (some d)) (hs : strictSite d = true) :
    ∃ o, (thread p L g).toMachine.Fired (some d) e o := by
  rcases d with ⟨s | ⟨i,d⟩,n⟩ <;>
    exact (Frame.trace (fun _ hg => restricted_sound hp hg) hX (Frame.lt_of_get hX he)).fired_at he
      (recover h hs)

theorem strict_fired_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {e : Event} (he : X.get (g,k) = some e)
    (h : Frame.stateAt (thread p L) X g k = some (some d)) (hs : strictSite d = true) :
    ∃ t ins o, (thread p L g).AtD d t ∧ (thread p L g).inv d ∧
      kernel.code[(thread p L g).pc d]? = some ins ∧
      Fires ((thread p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  rcases d with ⟨s | ⟨i,d⟩,n⟩ <;>
    exact Frame.fired_site (fun _ hg => restricted_sound hp hg) hX he (recover h hs)

theorem strict_end_at (hp : Pre p L m) (hg : g < L.threads) {t : TState}
    (hr : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (h : Frame.stateAt (thread p L) X g (X.tr g).length = some (some d))
    (hs : strictSite d = true) :
    ∃ t1 ins, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1 ∧
      (thread p L g).AtD d t1 ∧ (thread p L g).inv d ∧ kernel.code[(thread p L g).pc d]? =
      some ins ∧ out kernel Assumptions.all L g t1 =
        .ev (eventTmpl Assumptions.all L g t1 ins.op) := by
  rcases d with ⟨s | ⟨i,d⟩,n⟩ <;>
    exact Frame.end_at (fun _ hg => restricted_sound hp hg) hg hr (recover h hs)

theorem strict_pollsOn (hp : Pre p L m) (hg : g < L.threads)
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some d))
    (hs : strictSite d = true) {P : Event → Prop}
    (hS : ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, (thread p L g).AtD d t →
      (thread p L g).inv d → kernel.code[(thread p L g).pc d]? = some ins →
      Fires ((thread p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o → P e)
    {gd : Option (Nat × Bool)} {reg b : Nat} {off : Int} {par : Opnd} {sc : MbarScope}
    (hins : kernel.code[(thread p L g).pc d]? = some ⟨gd, .mbarWait reg b off par true sc⟩)
    {loc : Loc} {δ : Nat}
    (hub : ∀ f, ¬ P ⟨(thread p L g).pc d, .ub f⟩)
    (hev : ∀ l q ok sc', P ⟨(thread p L g).pc d, .wait l q ok true sc'⟩ →
      l = loc ∧ q % 2 = (okPolls loc (X.tr g) + δ) % 2) :
    Sched.PollsOn kernel Assumptions.all L X g loc δ := by
  rcases d with ⟨s | ⟨i,d⟩,n⟩ <;>
    exact Frame.pollsOn_of_shapeAt (fun _ hg => restricted_sound hp hg) hg (recover hσ hs)
      hS hins hub hev

end
end PTX.Kernels.TmlFa4Fwd.Proof
