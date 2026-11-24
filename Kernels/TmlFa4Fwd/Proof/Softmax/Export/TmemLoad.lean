-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax lane's score loads are followed by a `wait::ld`

A plain round's load (`sld .plain c`) waits at its own instruction's sub-step 1 (`sldw c`,
`k = 1`). The first and biased rounds' loads (`sld r c`) wait at the round's first P store at
sub-step 0 (`pst r 0`, `k = 0`, `delayedTmem`): between them the lane passes the round's bias
reads and barriers (`LdPend r`). From a load at position `f`, every later state of the lane is in
the region until a `wait::ld` or an undefined-behaviour event (`soft_ld_pend`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites between a first or biased round's loads and their wait. -/
def ldSites : Softmax.Rd → List Softmax.Site
  | .first => (List.finRange 4).map (.sld .first ·) ++ [.wb false] ++
      (List.finRange 16).map (.bld false ·) ++ [.fence false, .bsync false, .barr false,
      .narr .first]
  | .bias => (List.finRange 4).map (.sld .bias ·) ++ [.wb true] ++
      (List.finRange 16).map (.bld true ·) ++ [.fence true, .bsync true, .barr true,
      .stat false, .narr .bias]
  | .plain => []

/-- The states between a load of round `r` and its wait (the wait's state included). -/
def LdPend (r : Softmax.Rd) (d : Softmax.Control.D) : Prop :=
  d.site ∈ ldSites r ∨ (d.site = .pst r 0 ∧ d.k = 0 ∧ r ≠ .plain) ∨
    (∃ c, d.site = .sldw c ∧ d.k = 1 ∧ r = .plain)

/-- The wait states: a delayed P store at sub-step 0, an implicit wait at sub-step 1. -/
def LdWaitSt (d : Softmax.Control.D) : Prop :=
  (∃ r, d.site = .pst r 0 ∧ d.k = 0) ∨ (∃ c, d.site = .sldw c ∧ d.k = 1)

set_option maxHeartbeats 16000000 in
/-- The successor of a region state that is not the wait is in the region. -/
theorem ldp_next {r : Softmax.Rd} {d d' : Softmax.Control.D} {e : Event} (hp : LdPend r d)
    (hw : ¬ LdWaitSt d) (hn : Softmax.Control.succ p L g d e = some (some d')) : LdPend r d' := by
  obtain ⟨s, v, k, acc⟩ := d
  rcases hp with hm | ⟨hs, hk, -⟩ | ⟨c, hs, hk, -⟩
  · cases r <;> simp only [ldSites, List.mem_append, List.mem_map, List.mem_finRange, true_and,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    · rcases hm with (((⟨c, rfl⟩ | rfl) | ⟨c, rfl⟩) | rfl | rfl | rfl | rfl) <;>
        simp only [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ,
            Option.map_some, Option.map_none] at hn <;> (repeat' split at hn) <;> (try simp only
            [Option.map_none, Option.map_some, Option.some.injEq] at hn) <;>
        (first | (cases hn; done) | (cases hn; simp_all [LdPend, ldSites, Softmax.Control.erase,
            Softmax.D.mk',
          Softmax.afterLoads, Softmax.D.ite]; done) |
          (cases hn; simp only [Softmax.D.ite]; split <;>
            simp_all [LdPend, ldSites, Softmax.Control.erase, Softmax.D.mk']))
    · rcases hm with (((⟨c, rfl⟩ | rfl) | ⟨c, rfl⟩) | rfl | rfl | rfl | rfl | rfl) <;>
        simp only [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ,
            Option.map_some, Option.map_none] at hn <;> (repeat' split at hn) <;> (try simp only
            [Option.map_none, Option.map_some, Option.some.injEq] at hn) <;>
        (first | (cases hn; done) | (cases hn; simp_all [LdPend, ldSites, Softmax.Control.erase,
            Softmax.D.mk',
          Softmax.afterLoads, Softmax.D.ite]; done) |
          (cases hn; simp only [Softmax.D.ite]; split <;>
            simp_all [LdPend, ldSites, Softmax.Control.erase, Softmax.D.mk']))
  · exact absurd (.inl ⟨r, hs, hk⟩) hw
  · exact absurd (.inr ⟨c, hs, hk⟩) hw

set_option maxHeartbeats 4000000 in
/-- The successor of a load is in its round's region. -/
theorem sld_next {r : Softmax.Rd} {c : Fin 4} {v : Softmax.Control.V} {k : Fin 4} {acc : List Value}
    {d' : Softmax.Control.D} {e : Event}
    (hn : Softmax.Control.succ p L g ⟨.sld r c, v, k, acc⟩ e = some (some d')) :
    LdPend r d' := by
  cases r
  · exact ldp_next (.inl (by simp [ldSites])) (by rintro (⟨_, h, -⟩ | ⟨_, h, -⟩) <;> cases h) hn
  · exact ldp_next (.inl (by simp [ldSites])) (by rintro (⟨_, h, -⟩ | ⟨_, h, -⟩) <;> cases h) hn
  · simp only [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ, Option.map_some,
      Option.map_none] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | (cases hn; exact .inr (.inr ⟨c, rfl, rfl, rfl⟩))

set_option maxHeartbeats 8000000 in
/-- **From a score load, the lane stays in its round's region until a `wait::ld`** (or an
undefined-behaviour event). -/
theorem soft_ld_pend (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {f : Nat} {r0 : Softmax.Rd} {c0 : Fin 4} {v0 : Softmax.Control.V} {k0 : Fin 4} {a0 : List Value}
    {n0 : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g f =
      some (some (SmWarp.sinj p L g ⟨.sld r0 c0, v0, k0, a0⟩ n0))) :
    ∀ q, f < q → q ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g q = some (some σ) →
      (∃ w, f < w ∧ w < q ∧ ∃ pc, X.get (g, w) = some ⟨pc, .tc .waitLd⟩) ∨
      (∃ u, f < u ∧ u < q ∧ ∃ pc fl, X.get (g, u) = some ⟨pc, .ub fl⟩) ∨
      ∃ d n, σ = SmWarp.sinj p L g d n ∧ LdPend r0 d := by
  intro q
  induction q with
  | zero => intro h; omega
  | succ q ih =>
    intro hq hql σ' h'
    have heq : (X.tr g)[q]? = some ((X.tr g)[q]'(by omega)) := List.getElem?_eq_getElem _
    set eq := (X.tr g)[q]'(by omega)
    rw [Frame.stateAt_succ heq] at h'
    rcases hs : Frame.stateAt (thread p L) X g q with _ | _ | σ
    · rw [hs] at h'; cases h'
    · rw [hs] at h'; cases h'
    rw [hs] at h'
    have hn0 : ∀ d n, σ = SmWarp.sinj p L g d n → ∃ d', σ' = SmWarp.sinj p L g d'
        (Code.bump (Proof.cls L g) n eq) ∧ Softmax.Control.succ p L g d eq = some (some d') := by
      rintro d n rfl
      have hn : (thread p L g).next (SmWarp.sinj p L g d n) eq = some (some σ') := h'
      rw [SmWarp.next_sinj] at hn
      obtain ⟨o, ho1, ho⟩ := Option.map_eq_some_iff.mp hn
      cases o with
      | none => cases ho
      | some d' =>
        simp only [Option.map_some, Option.some.injEq] at ho
        exact ⟨d', ho.symm, ho1⟩
    rcases Nat.lt_or_ge f q with hfq | hfq
    · rcases ih hfq (by omega) σ hs with ⟨w, h1, h2, h3⟩ | ⟨u, h1, h2, h3⟩ |
        ⟨d, n, rfl, hpd⟩
      · exact .inl ⟨w, h1, by omega, h3⟩
      · exact .inr (.inl ⟨u, h1, by omega, h3⟩)
      obtain ⟨d', rfl, ho1⟩ := hn0 d n rfl
      by_cases hw : LdWaitSt d
      · have hget : X.get (g, q) = some eq := heq
        by_cases ub : ∃ f, eq.kind = .ub f
        · obtain ⟨fl, hk⟩ := ub
          exact .inr (.inl ⟨q, hfq, by omega, eq.pc, fl, hget.trans (congrArg some (congrArg
              (Event.mk eq.pc) hk))⟩)
        have hu : ∀ f, eq.kind ≠ .ub f := fun f h => ub ⟨f,h⟩
        have hev := (SmWarp.fired_soft hp hX hget hs hu).1.1
        obtain ⟨site, v, k1, a1⟩ := d
        rcases hw with ⟨r, hs', hk⟩ | ⟨c, hs', hk⟩ <;> simp only at hs' hk <;> subst hs' hk
        · cases r
          case plain =>
            exfalso
            rcases hpd with hm | ⟨h1, -, hpl⟩ | ⟨_, h, -⟩
            · cases r0 <;> simp [ldSites] at hm
            · simp only [Softmax.Site.pst.injEq] at h1; exact hpl h1.1.symm
            · cases h
          all_goals simp [Softmax.Control.D.scheduler, Softmax.Ev, Softmax.Site.delayed] at hev
          all_goals exact .inl ⟨q, hfq, by omega, eq.pc, by rw [hget, ← hev]⟩
        · simp [Softmax.Control.D.scheduler, Softmax.Ev] at hev
          rcases hev with hk' | ⟨fl, hk'⟩
          · exact .inl ⟨q, hfq, by omega, eq.pc, by rw [hget, ← hk']⟩
          · exact .inr (.inl ⟨q, hfq, by omega, eq.pc, fl, by rw [hget, ← hk']⟩)
      · exact .inr (.inr ⟨d', _, rfl, ldp_next hpd hw ho1⟩)
    · have : f = q := by omega
      subst this
      rw [hσ] at hs
      simp only [Option.some.injEq] at hs
      obtain ⟨d', rfl, ho1⟩ := hn0 _ _ hs.symm
      exact .inr (.inr ⟨d', _, rfl, sld_next ho1⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof
