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

/-! # A softmax lane's P stores are followed by a `wait::st` of their round

The P stores of a round `r` (`pst r q`) wait at `pwst r k`: stores 0 to 2 at `pwst r 0`, store 3
at `pwst r 1` (`pstNext`). From a P store at position `f`, every later state of the lane is a
P store or a store wait of the round (`PstPend r`) until a `wait::st` (the event at `pwst`) or an
undefined-behaviour event (`soft_st_pend`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The P stores and store waits of round `r`. -/
def PstPend (r : Softmax.Rd) : Softmax.Site → Bool
  | .pst r' _ | .pwst r' _ => r' == r
  | _ => false

/-- The successor of a P store of round `r` is a P store or store wait of the round. -/
private theorem pst_data_next {r : Softmax.Rd} {d d' : Softmax.D} {e : Event}
    (hp : PstPend r d.site = true) (hw : ∀ k, d.site ≠ .pwst r k)
    (hn : Softmax.succ p L g d e = some (some d')) : PstPend r d'.site = true := by
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> (try simp only [PstPend, Bool.false_eq_true] at hp)
  case pst r' q =>
    simp only [PstPend, beq_iff_eq] at hp
    subst hp
    cases r' <;> fin_cases q <;> simp only [Softmax.succ, Softmax.pstNext] at hn <;>
      (try split_ifs at hn) <;> cases hn <;> simp [PstPend, Softmax.D.mk']
  case pwst r' k' =>
    simp only [PstPend, beq_iff_eq] at hp
    subst hp
    exact absurd rfl (hw k')

theorem pst_next {r : Softmax.Rd} {d d' : Softmax.Control.D} {e : Event}
    (hp : PstPend r d.site = true) (hw : ∀ k, d.site ≠ .pwst r k)
    (hn : Softmax.Control.succ p L g d e = some (some d')) : PstPend r d'.site = true := by
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> (try simp only [PstPend, Bool.false_eq_true] at hp)
  case pst r' q =>
    simp only [PstPend, beq_iff_eq] at hp
    subst hp
    change (Softmax.succ p L g _ e).map (Option.map Softmax.Control.erase) = _ at hn
    obtain ⟨x,hx,hm⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨a,rfl,rfl⟩ := Option.map_eq_some_iff.mp hm
    exact pst_data_next (d := Softmax.Control.D.scheduler ⟨.pst r' q,v,k,acc⟩)
      (r := r') (by simp [PstPend, Softmax.Control.D.scheduler]) (by intro j; nofun) hx
  case pwst r' k' =>
    simp only [PstPend, beq_iff_eq] at hp
    subst hp
    exact absurd rfl (hw k')

set_option maxHeartbeats 8000000 in
/-- **From a P store, the lane stays among its round's P stores and store waits until a
`wait::st`** (or an undefined-behaviour event). -/
theorem soft_st_pend (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {f : Nat} {r0 : Softmax.Rd} {q0 : Fin 4} {v0 : Softmax.Control.V} {k0 : Fin 4} {a0 : List Value}
    {n0 : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g f =
      some (some (SmWarp.sinj p L g ⟨.pst r0 q0, v0, k0, a0⟩ n0))) :
    ∀ q, f < q → q ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g q = some (some σ) →
      (∃ w, f < w ∧ w < q ∧ ∃ pc, X.get (g, w) = some ⟨pc, .tc .waitSt⟩) ∨
      (∃ u, f < u ∧ u < q ∧ ∃ pc fl, X.get (g, u) = some ⟨pc, .ub fl⟩) ∨
      ∃ d n, σ = SmWarp.sinj p L g d n ∧ PstPend r0 d.site = true := by
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
    have hpre : (∃ w, f < w ∧ w < q + 1 ∧ ∃ pc, X.get (g, w) = some ⟨pc, .tc .waitSt⟩) ∨
        (∃ u, f < u ∧ u < q + 1 ∧ ∃ pc fl, X.get (g, u) = some ⟨pc, .ub fl⟩) ∨
        ∃ d n, σ = SmWarp.sinj p L g d n ∧ PstPend r0 d.site = true := by
      rcases Nat.lt_or_ge f q with hfq | hfq
      · rcases ih hfq (by omega) σ hs with ⟨w, h1, h2, h3⟩ | ⟨u, h1, h2, h3⟩ | h
        · exact .inl ⟨w, h1, by omega, h3⟩
        · exact .inr (.inl ⟨u, h1, by omega, h3⟩)
        · exact .inr (.inr h)
      · have : f = q := by omega
        subst this
        rw [hσ] at hs
        simp only [Option.some.injEq] at hs
        exact .inr (.inr ⟨_, _, hs.symm, by simp [PstPend]⟩)
    rcases hpre with h | h | ⟨d, n, rfl, hpd⟩
    · exact .inl h
    · exact .inr (.inl h)
    have hn : (thread p L g).next (SmWarp.sinj p L g d n) eq = some (some σ') := h'
    rw [SmWarp.next_sinj] at hn
    obtain ⟨o, ho1, ho⟩ := Option.map_eq_some_iff.mp hn
    cases o with
    | none => cases ho
    | some d' =>
      simp only [Option.map_some, Option.some.injEq] at ho
      subst ho
      by_cases hw : ∃ k, d.site = .pwst r0 k
      · obtain ⟨k, hs'⟩ := hw
        have hget : X.get (g, q) = some eq := heq
        have hfq : f < q := by
          rcases Nat.lt_or_ge f q with h | h
          · exact h
          · exfalso
            have : f = q := by omega
            subst this
            rw [hσ] at hs
            obtain ⟨site, v, k1, a1⟩ := d
            simp only at hs'
            subst hs'
            simp at hs
        by_cases ub : ∃ f, eq.kind = .ub f
        · obtain ⟨fl, hk⟩ := ub
          exact .inr (.inl ⟨q, hfq, by omega, eq.pc, fl, hget.trans (congrArg some (congrArg
              (Event.mk eq.pc) hk))⟩)
        have hu : ∀ f, eq.kind ≠ .ub f := fun f h => ub ⟨f,h⟩
        have hev := (SmWarp.fired_soft hp hX hget hs hu).1.1
        obtain ⟨site, v, k1, a1⟩ := d
        simp only at hs'
        subst hs'
        simp only [Softmax.Control.D.scheduler, Softmax.Ev] at hev
        rcases hev with hk | ⟨fl, hk⟩
        · exact .inl ⟨q, hfq, by omega, eq.pc, by rw [hget, ← hk]⟩
        · exact .inr (.inl ⟨q, hfq, by omega, eq.pc, fl, by rw [hget, ← hk]⟩)
      · push Not at hw
        exact .inr (.inr ⟨d', _, rfl, pst_next hpd hw ho1⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof
