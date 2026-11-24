-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Where the softmax machine stops

The machine stops (`some none`) exactly on a returned value of another kind than its site's
(`ret`, the `stop_iff` field of `Fragment.OkAt`): a 32-bit word at the scheduler's reads and
shuffles and at the request's reads, and on an element that is not an `f32` payload at the score
loads. The bias loads, the polls and the election record whatever they return; a plain round's
implicit wait is entered at sub-step 1 only (the invariant), where the machine moves on. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {g : Nat}

/-- The kind of value each site returns: a 32-bit word at a read or shuffle of the scheduler and
at the request's reads, `f32` reals at the score loads, two `bf16` payloads or masked halves at
the bias loads. -/
def ret (d : D) : RetKind :=
  match d.site with
  | .word _ | .q0 | .q1 | .uk | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ => .word 32
  | .sld _ _ => .real .f32
  | .bld _ _ => .packedWith .bf16 (maskedElem .bf16 0xFF80)
  | _ => .none

/-- At a bias load the machine stops exactly on a word that is not two `bf16` payloads or
masked halves. -/
theorem stop_bld (b : Bool) (c : Fin 16) (v : V) (k : Fin 4) (acc : List Value) {e : Event}
    (hev : Ev p L g ⟨.bld b c, v, k, acc⟩ e) :
    (code p L g).next ⟨.bld b c, v, k, acc⟩ e = some none ↔
      ¬ (ret ⟨.bld b c, v, k, acc⟩).accepts e := by
  obtain ⟨pc, kd⟩ := e
  simp only [Ev, rdOrUb] at hev
  rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk
  · simp only [ret, RetKind.accepts, recvAll, recv, code, succ]
    cases rebuild 3 bs with
    | error f => simp
    | ok x =>
      simp only [Option.toList_some, List.mem_singleton, forall_eq, RetKind.acceptsVal]
      by_cases hx : biasOk x = true
      · simp only [hx, ↓reduceIte]
        simp only [not_true_eq_false, iff_false]
        split <;> simp
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        simp only [not_false_eq_true]
  · simp [ret, succ, code, RetKind.accepts, recvAll, recv]

/-- At a score load the machine stops exactly on an element that is not an `f32` payload. -/
theorem stop_sld (r : Rd) (c : Fin 4) (v : V) (k : Fin 4) (acc : List Value) {e : Event}
    (hev : Ev p L g ⟨.sld r c, v, k, acc⟩ e) :
    (code p L g).next ⟨.sld r c, v, k, acc⟩ e = some none ↔
      ¬ (ret ⟨.sld r c, v, k, acc⟩).accepts e := by
  obtain ⟨pc, kd⟩ := e
  simp only [Ev, tcLdOrUb] at hev
  rcases hev with ⟨a, vals, sh, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk
  · rw [RetKind.accepts_tcLd rfl]
    simp only [ret, RetKind.acceptsVal, code, succ]
    rw [← flAll_eq_none_iff]
    cases flAll vals <;> cases r <;> simp
  · simp [ret, succ, code, RetKind.accepts, recvAll, recv]

/-- **The machine stops exactly on a returned value of another kind than its site's.** -/
theorem stop_iff (d : D) : ∀ {e : Event}, (code p L g).inv d → Ev p L g d e →
    ((code p L g).next d e = some none ↔ ¬ (ret d).accepts e) := by
  obtain ⟨s, v, k, acc⟩ := d
  stop_cases s skip_by (first
    | (intro e _ hev; exact stop_sld _ _ _ _ _ hev)
    | (intro e _ hev; exact stop_bld _ _ _ _ _ hev)
    | (
      intro e hi _
      have hk : k = 1 := by
        rcases hi with ⟨-, -, hf⟩ | ⟨hk, -⟩
        · simp [Site.first] at hf
        · exact hk
      subst hk
      simp [ret, succ, RetKind.accepts_none]))
    unfolding [Ev, Int.reduceToNat, Nat.reduceAdd, Nat.reduceMod, Nat.reduceBEq, ite_true,
      ite_false, pollOff, pollW, arrOff, Site.toE, Site.delayed, rdOrUb, tcLdOrUb, votePredS,
      ctaOf, Epilogue.Ev, Epilogue.partialAt]
    trans [ret, succ, word32, scAt, D.mk', D.ite, afterTotal, loopHead, scanExit, passStart,
      afterTiles, afterRound, afterFirst, afterBias, afterPlain, plainEntry, afterLoads, pstNext]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
