-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.Code

@[expose] public section

/-! # The targets of a Tensor Core commit

A proof tool. A commit event's specification is resolved over the issuing thread's CTA
(`commit_resolves`, THREAD-TC-COMMIT-TARGETS), so each of its targets is a CTA of the issuer's
cluster (`target_cta`). The event of a code machine's state is undefined behaviour or the event
of the instruction at its program counter (`Code.fired_op`), so this holds of every event a
code machine follows, followed or not. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A template whose commit, if it is one, resolves over CTA `issuer` with group `group`. -/
def CommitResolves (L : Launch) (group : CtaGroup) (issuer : Nat) : Tmpl → Prop
  | .tc (.commit s) _ => ∃ m bits, TcCommit.resolve L group issuer m bits = some s
  | _ => True

theorem ofExec_commitResolves {L : Launch} {group : CtaGroup} {issuer : Nat} {r : Exec Tmpl}
    (h : PTX.EventFrame.AllOk (CommitResolves L group issuer) r) :
    CommitResolves L group issuer (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- A `tcgen05.commit` fires a commit whose specification resolves over the issuer's CTA. -/
theorem tcCommit_resolves {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {mask : Option Opnd} {pc : Nat} {e : Event}
    {o : Option TState} {s : TcCommit.Spec}
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off mask)) e o)
    (hk : e.kind = .tc (.commit s)) :
    ∃ m bits, TcCommit.resolve L group (g / L.block) m bits = some s := by
  have hr : CommitResolves L group (g / L.block) (eventTmpl A L g t (.tcCommit group base off mask))
    := by
    simp only [eventTmpl, tcCommitTmpl]
    repeat' first
      | trivial
      | (apply ofExec_commitResolves)
      | (apply PTX.EventFrame.allOk_bind; intro _)
      | exact ⟨_, _, ‹_›⟩
      | split
  generalize eventTmpl A L g t (.tcCommit group base off mask) = m at hf hr
  cases m <;> simp only [Fires] at hf <;> (try simp only [CommitResolves] at hr) <;>
    first
      | (obtain ⟨rfl, -⟩ := hf; cases hk; exact hr)
      | aesop

/-- Every commit event's specification resolves over the issuer's CTA. -/
theorem commit_resolves {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} {s : TcCommit.Spec}
    (hf : Fires pc (eventTmpl A L g t op) e o) (hk : e.kind = .tc (.commit s)) :
    ∃ group m bits, TcCommit.resolve L group (g / L.block) m bits = some s := by
  cases hop : commitOp op
  · exact absurd hk (fires_notCommit (eventTmpl_notCommit (commitOp_ne hop)) hf s)
  · cases op <;> simp only [commitOp, Bool.false_eq_true] at hop
    obtain ⟨m, bits, h⟩ := tcCommit_resolves hf hk
    exact ⟨_, m, bits, h⟩

/-- A target of a resolved commit is a CTA of the issuer's cluster: rank `r` of that cluster. -/
theorem target_cta {L : Launch} {group : CtaGroup} {issuer : Nat} {mbar : Loc}
    {bits : BitVec 16} {s : TcCommit.Spec} {r : Fin 16} {m : Loc}
    (hs : TcCommit.resolve L group issuer mbar bits = some s) (ht : TcCommit.target s r = some m) :
    r.val < L.clusterSizeOf issuer ∧
      m.cta = L.clusterStart (L.clusterOfCta issuer) + r.val := by
  unfold TcCommit.resolve at hs
  split_ifs at hs
  cases hs
  unfold TcCommit.target at ht
  split_ifs at ht with hr
  cases ht
  exact ⟨hr.1, rfl⟩

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- An output of the instruction at a thread state's program counter is undefined behaviour or
the instruction's event template. -/
theorem out_ev {t : TState} {m : Tmpl} (h : out K A L g t = .ev m) :
    (∃ f, m = .ub f) ∨ ∃ ins, K.code[t.pc]? = some ins ∧ m = eventTmpl A L g t ins.op := by
  unfold out at h
  repeat' split at h
  all_goals first
    | (cases h; exact .inl ⟨_, rfl⟩)
    | (cases h; exact .inr ⟨_, ‹K.code[t.pc]? = some _›, rfl⟩)
    | nomatch h

/-- **An event a code machine fires** is undefined behaviour or the event of the instruction
at its thread state's program counter. -/
theorem Code.fired_op {C : Code K A L g} {σ : Option C.D} {e : Event} {o : Option TState}
    (hf : C.toMachine.Fired σ e o) :
    (∃ pc f, e = ⟨pc, .ub f⟩) ∨
      ∃ t ins, K.code[t.pc]? = some ins ∧ Fires t.pc (eventTmpl A L g t ins.op) e o := by
  obtain ⟨t, hg, hfire⟩ := hf
  have hub : ∀ f, Fires t.pc (.ub f) e o → ∃ pc f, e = ⟨pc, .ub f⟩ :=
    fun f h => ⟨_, f, h.1⟩
  cases σ with
  | none =>
    obtain ⟨m, hm⟩ := hg
    change Fires t.pc (Code.tmpl C none t) e o at hfire
    simp only [Code.tmpl, hm] at hfire
    rcases out_ev hm with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
    · exact .inl (hub f hfire)
    · exact .inr ⟨t, ins, hc, hfire⟩
  | some d =>
    change Fires t.pc (Code.tmpl C (some d) t) e o at hfire
    simp only [Code.tmpl] at hfire
    split at hfire
    · rename_i ins hc
      rw [← hg.1.1] at hc
      exact .inr ⟨t, ins, hc, hfire⟩
    · exact .inl (hub _ hfire)

end
end PTX.Flow
