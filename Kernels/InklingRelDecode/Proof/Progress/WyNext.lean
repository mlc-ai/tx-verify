-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Polls
public import Kernels.InklingRelDecode.Proof.Interface.WyPoll

@[expose] public section

/-!
# The next event of a thread at a poll

The first clause of `Sched.PollBlocked`: a released pending thread of a maximal execution whose
state's next event is an mbarrier poll (`nextKind s = .wait`) reaches, from every run of its trace
and for either outcome, the poll of one object with one parity at one position. The object and the
parity are functions of the abstract state (`Interface.PollAt`, the six poll sites).

The proof: the machine's site at the end of the run fires the instruction's template
(`Frame.end_at`); a template of undefined behaviour would extend the maximal execution
(`ub_ext`), so the template is a poll (`tmpl_kind`); every event it fires is a continuing event
fired from the state, whose shape `Interface.poll_site` gives.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
  {g : Nat}

/-- The instruction of a state whose next event is a poll is an `mbarrier.try_wait`. -/
theorem waitOp_of_kind {s : TSt} (hk : nextKind s = .wait) :
    ∃ ins, kernel.code[TSt.pc s]? = some ins ∧ isWaitOp ins.op = true := by
  unfold nextKind at hk
  split at hk
  · rename_i ins hc
    refine ⟨ins, hc, ?_⟩
    revert hk
    generalize ins.op = op
    intro hk
    cases op <;> simp only [opKindSub, opKind, isWaitOp] at hk ⊢ <;> (try split at hk) <;>
      (try split at hk) <;> (try split_ifs at hk) <;> simp_all
  · cases hk

/-- **The template at the end of a run of a released pending thread at a poll is a poll**: from
the run's last state, local steps reach a concrete state of the machine state whose template polls
an object, and every outcome of that poll is an event fired from the machine state. A template of
undefined behaviour would extend the maximal execution by a counted event. -/
theorem wait_next (hmax : Maximal L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) {s : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some s)) (hk : nextKind s = .wait) {t : TState}
    (hrun : Run kernel asms L g {} (X.tr g) (some t)) :
    ∃ t1 l p kk a sc, Relation.ReflTransGen (Tau kernel asms L g) t t1 ∧
      out kernel asms L g t1 = .ev (.wait l p kk a sc) ∧
      ∀ ok, (threadCode L g Q).toMachine.Fired (some s) ⟨t1.pc, .wait l p ok a sc⟩
        (some (kk ok)) := by
  obtain ⟨t1, ins, hl, hat, hinv, hc, hout⟩ := Frame.end_at (C := code L Q) hS hp.1 hrun hσ
  have hkind := tmpl_kind hat hc (kind_ne_other (hS g hp.1) hinv hc)
  rw [hk] at hkind
  rcases hkind with ⟨f, hf⟩ | ⟨l, p, kk, a, sc, hm⟩
  · rw [hf] at hout
    obtain ⟨Y, hY, hle, hlt⟩ := ub_ext hmax.1 hp.1 hrel hrun hl hout
    exact absurd (hmax.2 Y hY hle) (by omega)
  · refine ⟨t1, l, p, kk, a, sc, hl, hm ▸ hout, fun ok => ⟨t1, ⟨hat, hinv⟩, ?_⟩⟩
    change Fires t1.pc (Code.tmpl (threadCode L g Q) (some s) t1) _ _
    simp only [Code.tmpl]
    have hc' : kernel.code[s.pc]? = some ins := hc
    rw [hc']
    simp only
    rw [hm]
    exact ⟨ok, rfl, rfl⟩

/-- **The first clause of `Sched.PollBlocked`**: a released pending thread of a maximal execution at
a poll reaches, from every run and for either outcome, the poll of the object and parity `PollAt`
names, at one position. -/
theorem poll_next (hpre : Pre Q L mem0) (hmax : Maximal L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hrg : LdRng Q L X) (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) {s : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some s)) (hk : nextKind s = .wait) :
    ∃ m pcw par, PollAt L g s m par ∧
      ∀ t, Run kernel asms L g {} (X.tr g) (some t) → ∀ ok : Bool,
        ∃ t1 u sc, Relation.ReflTransGen (Tau kernel asms L g) t t1 ∧
          EStep kernel asms L g t1 ⟨pcw, .wait m par ok true sc⟩ (some u) := by
  obtain ⟨ins, hc, hop⟩ := waitOp_of_kind hk
  obtain ⟨m, pcw, par, hat, hsh⟩ := poll_site hpre hrg hp.1 hσ hc hop
  refine ⟨m, pcw, par, hat, fun t hrun ok => ?_⟩
  obtain ⟨t1, l, p, kk, a, sc, hl, hout, hF⟩ := wait_next hmax hS hp hrel hσ hk hrun
  obtain ⟨ok', he⟩ := hsh _ _ (hF ok)
  simp only [Event.mk.injEq, Kind.wait.injEq] at he
  obtain ⟨hpc, rfl, rfl, rfl, rfl, rfl⟩ := he
  exact ⟨t1, kk ok, .cta, hl, _, hout, ok, by rw [hpc], rfl⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
