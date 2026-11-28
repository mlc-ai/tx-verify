-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Shape
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.NoUbQ
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos

@[expose] public section

/-! # The MMA warp makes no undefined behaviour

`mma_noUb`: an event fired from a state of the MMA warp of a followed lane is no undefined
behaviour, and the machine stops at it only if it is the exit. The state before the event is
strictly good (`strict_event_nontma`), so the event is the template of its site, and each site's
operands pass their checks (`Mma/NoUbSite.lean`, `Mma/NoUbQ.lean`):

* the election's mask is the full warp, the length loads read their row's word through a set
  pointer (`SiteOk`), and the machine continues with it (`next_topk`, `next_extra`);
* the trap is not reached (`mma_no_trap`): a state at the trap records the launch's length
  words (`mma_words_of`, after the election the one counted election gives) whose padded total
  passes the test (`blocksOf_pos`), yet the trap is built only by a failing test
  (`succ_trapC`);
* the polls and commits name aligned words of the CTA's block, the stage word being `0` or `1`
  in the block loop (`LoopOk`); the query loads, the copies and both forms of MMA have operands
  that read and decode. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The padded total of a launch's two length words is at least 64. -/
private theorem total_gt {d : Mma.D} (h0 : d.l0 = lenWA P L (g / L.block))
    (h1 : d.l1 = lenWB P L (g / L.block)) (hp : Pre P L m) :
    Arith32.scmpi .gt .s (Mma.r27 d.l0 d.l1) 63 = true := by
  have hb := blocksOf_pos hp (g / L.block)
  rw [blocksOf, ← h0, ← h1] at hb
  have hlt : Arith32.scmpi .lt .s (totL d.l0 d.l1) 64 = false := by
    cases ht : Arith32.scmpi .lt .s (totL d.l0 d.l1) 64
    · rfl
    · simp [roundsOf, ht] at hb
  have hr : Mma.r27 d.l0 d.l1 = totL d.l0 d.l1 := (totL_eq _ _).symm
  rw [hr]
  unfold Arith32.scmpi at hlt ⊢
  unfold PTX.compare at hlt ⊢
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hlt ⊢
  have h64 : toSigned 32 (Arith32.i32 64) = 64 := by decide
  have h63 : toSigned 32 (Arith32.i32 63) = 63 := by decide
  omega

/-- **The trap is not reached**: a state at the trap records the launch's words, whose total
passes the test. -/
private theorem mma_no_trap (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)))
    (hcore : Mma.RefCore L g d fun c => n (.mma c)) (ht : d.site = .trap) : False := by
  have h1 := Mma.elect_one hcore (by rw [ht]; decide)
  obtain ⟨j, hjk, inst, hj⟩ := mma_won_of hp hX hFw hσ h1
  obtain ⟨d', n', heq, -, hok⟩ := mma_words_of hp hX hFw hj hjk hσ
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at heq
  obtain ⟨rfl, -⟩ := heq
  simp only [mmaWordsOk, ht] at hok
  obtain ⟨h0, h1, hq⟩ := hok
  rw [total_gt h0 h1 hp] at hq
  cases hq

/-- **The MMA warp makes no undefined behaviour.** -/
theorem mma_noUb (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X)
    (g k : Nat) (e : Event) (he : X.get (g, k) = some e) (ha : AliveIn P L X g k .mma) :
    (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
  obtain ⟨σ, hσ, hr⟩ := aliveIn_iff.mp ha
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, ins, hgood, hc, hf⟩ := strict_event_nontma hp hX he hσ (.inr hr)
  obtain ⟨hat, hinv⟩ := hgood
  have hJ := (follow_iff.mp hFw g hg k).2 σ hσ
  have hRole := state_role hJ hinv
  cases hr with
  | mma d n =>
    cases hRole with
    | mma d' n' hR hok hl hw hpc hrg =>
      have hu : n (.mma .ub) = 0 := (state_count hσ (.mma .ub)).trans (take_noUb hX he)
      have hcore := hR (state_ub hX hσ he) hu
      have hph : ∀ {s : Mma.Site}, d.site = s → s.inLoop = true →
          ∃ b : Fin 2, d.pha = W b.val := fun hs' hl' => by
        obtain ⟨⟨-, -, -, -, -, hq, -, -⟩, -⟩ := (Mma.core_loop (hs' ▸ hl')).mp hcore
        exact ⟨⟨_, Nat.mod_lt _ (by decide)⟩, hq⟩
      have hev := Mma.shape hp hat hinv.1 hc hf
      have hkind : Mma.EvK L g d e := hev.2
      have hnt : d.site ≠ .trap := fun ht => mma_no_trap hp hX hFw hσ hcore ht
      have hsimple : (d.site = .qArrive ∨ d.site = .qFence ∨ d.site = .qCopyFence ∨
          d.site = .kvFence ∨ d.site = .soFence ∨ d.site = .outBar ∨ d.site = .exit) →
          ∀ f, e.kind ≠ .ub f := by
        intro h f
        rcases h with h | h | h | h | h | h | h <;>
          (simp only [Mma.EvK, h] at hkind; rw [hkind]; intro h; cases h)
      have hub : ∀ f, e.kind ≠ .ub f := by
        cases hs : d.site with
        | elect => exact Mma.noUb_elect d hs hat hinv.1 hc hf
        | loadTopk => exact Mma.noUb_loadTopk hp d hs (hok.1 hs) hat hinv.1 hc hf
        | loadExtra => exact Mma.noUb_loadExtra hp d hs (hok.2.1 hs) hat hinv.1 hc hf
        | trap => exact absurd hs hnt
        | qLoad i => exact Mma.noUb_qLoad hp hg d ⟨i, hs⟩ hat hinv.1 hc hf
        | qWait => exact Mma.noUb_qWait hp d hs hat hinv.1 hc hf
        | qCopyWait => exact Mma.noUb_qCopyWait hp d hs hat hinv.1 hc hf
        | qCopy i => exact Mma.noUb_qCopy hp hg d ⟨i, hs⟩ hat hinv.1 hc hf
        | qCopyCommit => exact Mma.noUb_qCopyCommit hp hg d hs hat hinv.1 hc hf
        | kvWait => exact Mma.noUb_kvWait hp d hs (hph hs rfl) hat hinv.1 hc hf
        | soWait => exact Mma.noUb_soWait hp d hs (hph hs rfl) hat hinv.1 hc hf
        | qk i => exact Mma.noUb_qk hp hg d ⟨i, hs⟩ (hph hs rfl) hat hinv.1 hc hf
        | qkCommit => exact Mma.noUb_qkCommit hp hg d hs (hph hs rfl) hat hinv.1 hc hf
        | pv i => exact Mma.noUb_pv hp hg d ⟨i, hs⟩ (hph hs rfl) hat hinv.1 hc hf
        | pvCommit => exact Mma.noUb_pvCommit hp hg d hs (hph hs rfl) hat hinv.1 hc hf
        | leave i => exact absurd hs (hl i)
        | qArrive => exact hsimple (.inl hs)
        | qFence => exact hsimple (.inr (.inl hs))
        | qCopyFence => exact hsimple (.inr (.inr (.inl hs)))
        | kvFence => exact hsimple (.inr (.inr (.inr (.inl hs))))
        | soFence => exact hsimple (.inr (.inr (.inr (.inr (.inl hs)))))
        | outBar => exact hsimple (.inr (.inr (.inr (.inr (.inr (.inl hs))))))
        | exit => exact hsimple (.inr (.inr (.inr (.inr (.inr (.inr hs))))))
      refine ⟨hub, fun hs => ?_⟩
      have hn : Mma.succ P L g d e = none := thread_next_none_sub (next_none_of_stops he hσ hs)
      obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
      cases site with
      | exit => simpa only [Mma.EvK] using hkind
      | trap => exact absurd rfl hnt
      | elect =>
        simp only [Mma.EvK] at hkind
        rcases hkind with ⟨inst, ld, hk⟩ | ⟨f, hk⟩
        · simp [Mma.succ, hk] at hn
        · exact absurd hk (hub f)
      | loadTopk =>
        rw [Mma.next_topk hp hX he hok hat hc hf] at hn
        cases hn
      | loadExtra =>
        rw [Mma.next_extra hp hX he hok hat hc hf] at hn
        cases hn
      | qWait | qCopyWait | kvWait | soWait =>
        simp only [Mma.EvK, Mma.PollEv] at hkind
        rcases hkind with ⟨ok, hk⟩ | ⟨f, hk⟩
        · simp [Mma.succ, Mma.poll, hk] at hn
        · exact absurd hk (hub f)
      | leave i => exact absurd rfl (hl i)
      | _ => simp [Mma.succ] at hn

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
