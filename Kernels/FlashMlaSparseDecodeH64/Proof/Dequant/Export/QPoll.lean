-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Pred

@[expose] public section

/-! # A dequant lane's store follows its Q poll

A dequant lane enters its block loop only through the successful poll of `qUtccp` at pc 2644
(site `wq`); every state of the loop is reached from `wq` by that poll or from a loop state, so a
loop event, in particular a chunk store, follows the lane's poll of `qUtccp` in program order
(`dequant_qPoll`), which the Q ring's query copy is observed by (`qUtccp_observes`). The walk is
`deq_pred` backwards from the state of the store. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites of the block loop. -/
private def LoopSite : Dequant.Site → Bool
  | .wraw | .wsv | .scale _ | .raw _ _ | .store _ _ | .fpx | .arrD | .arrF => true
  | _ => false

/-- A loop state follows a loop state, or the Q poll's state on the poll's event. -/
private theorem succ_loop {d' d : Dequant.Control.D} {f : Event}
    (h : Dequant.Control.succ P L g d' f = some (some d)) (hd : LoopSite d.site = true) :
    LoopSite d'.site = true ∨ (d'.site = .wq ∧ ∃ x y a b, f.kind = .wait x y true a b) := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d'
  cases site
  case wq =>
    right
    refine ⟨rfl, ?_⟩
    obtain ⟨pc, k⟩ := f
    cases k <;> simp only [Dequant.Control.succ] at h <;> try (cases h; done)
    rename_i x y ok a b
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [LoopSite] at hd
    · exact ⟨x, y, a, b, rfl⟩
  all_goals
    simp only [Dequant.Control.succ, Dequant.Control.poll, Dequant.Control.dataRd,
      Dequant.Control.afterSmr, Dequant.Control.afterA,
      Dequant.Control.advance, Dequant.Control.scaleNext, Code.ncNext] at h
    repeat' split at h
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst h
    all_goals simp [LoopSite] at hd ⊢

/-- **The loop states follow the Q poll**: a state of the block loop at index `i ≤ k` of a lane
with an event at `k` follows the lane's successful poll of `qUtccp` at pc 2644. -/
private theorem loop_qpoll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    ∀ i, i ≤ k → ∀ (d : Dequant.Control.D) (n : Cls → Nat),
      Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .dequant, d⟩, n)) →
      LoopSite d.site = true →
      ∃ j < i, X.get (g, j) =
        some ⟨2644, .wait (mbarLoc L (g / L.block) .qUtccp) 0 true true .cta⟩ := by
  intro i
  induction i with
  | zero =>
    intro _ d n hs
    obtain ⟨i', hi'⟩ := deq_pred_index hs
    omega
  | succ i ih =>
    intro hik d n hs hd
    obtain ⟨f, hf, hub⟩ := deq_earlier_ev hX he (by omega : i < k)
    obtain ⟨d', n', hs', hsucc⟩ := deq_pred hFw hg hf hs
      (by intro h; rw [h] at hd; simp [LoopSite] at hd)
    rcases succ_loop hsucc hd with h1 | ⟨hwq, x, y, a, b, hk⟩
    · obtain ⟨j, hj, hget⟩ := ih (by omega) d' n' hs' h1
      exact ⟨j, by omega, hget⟩
    · refine ⟨i, by omega, ?_⟩
      obtain ⟨hpc, hk'⟩ := deq_ev hp hX hFw hf hub hs'
      obtain ⟨pc, kd⟩ := f
      simp only [Dequant.EvK, hwq, Dequant.PollEv] at hk' hpc hk
      subst hk
      rcases hk' with ⟨ok, hk'⟩ | ⟨f', hk'⟩
      · simp only [Kind.wait.injEq] at hk'
        obtain ⟨h1, h2, -, h3, h4⟩ := hk'
        subst h1 h3 h4
        have h5 : (truncBits 32 (Arith32.i32 0)).toNat % 2 = 0 := by decide
        rw [h5] at h2
        subst h2
        rw [hpc, Dequant.q_loc hp] at hf
        exact hf
      · cases hk'

/-- **A dequant lane's store follows its poll of `qUtccp`**: a store of a lane of warpgroup 2 at
a pc of its code is preceded in program order by the lane's successful poll of `qUtccp` of its
CTA at pc 2644. -/
theorem dequant_qPoll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : DequantAt L g pc) :
    ∃ j < k, X.get (g, j) =
      some ⟨2644, .wait (mbarLoc L (g / L.block) .qUtccp) 0 true true .cta⟩ := by
  obtain ⟨-, -, hlo, hhi⟩ := hat
  have hg := Frame.lt_of_get hX he
  have hub : ∀ fl, Kind.wr a bs ≠ .ub fl := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc
    ⟨hlo, hhi⟩
  have hl : LoopSite d.site = true := by
    obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
    cases site <;>
      simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv, LoopSite] at hk ⊢
  exact loop_qpoll hp hX hFw hg he k le_rfl d n hσ hl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
