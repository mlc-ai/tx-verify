-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Vote
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumVoteIn
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part009
import Lemmas.Flow.RoleStep
import Lemmas.Flow.VoteIn
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The input of the rescale vote, off the trace

The vote event of a lane of warpgroup 0 (pc 578) records the lane's predicate: `w0VoteIn` of the
trace before it (`w0_vote_input`): the block in progress's own and peer maxima against the carried
maximum. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The input of a vote** (valid rows): a vote event of lane `g` at pc 578 records
`w0VoteIn` of the trace before it. -/
theorem w0_vote_input (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 578)
    (hv : W0Valid P.scale ((X.tr g).take (k + 1))) :
    ∀ q a r, e.kind = .voteMode q (2 ^ 32 - 1) a r → a = w0VoteIn P.scale ((X.tr g).take k) := by
  intro q a r hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hx := w0_scale_rd hp
  have hvk : W0Valid P.scale ((X.tr g).take k) := by
    have := hv.take (j := k)
    rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  obtain ⟨st, hst, hslot, hpre, hI, -⟩ := followW hp hX hFw hw he hub hx hvk k le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he hst hub
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e.pc = (thread P L g).pc (.inl b, n) := hpc'
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  obtain ⟨hIW, hOk, hCar, hVote, -⟩ := hI d rfl
  have hsite : d.c.site = .vote := Wg0.site_vote_of_pc (hpc'.symm.trans hpc)
  have hok : d.ok = true := hOk (by rw [hsite]; rfl)
  obtain ⟨hm, hl, hmx, -⟩ := hCar hok (by rw [hsite]; rfl)
  -- the block in progress after the vote has the words of the block before it
  have hetake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
    rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some]
  have hfin : w0Fin ((X.tr g).take (k + 1)) = ((w0Fin ((X.tr g).take k)).1,
      (w0Fin ((X.tr g).take k)).2 ++ [e]) := by
    rw [hetake]
    exact w0Fin_ext _ _ (fun e' he' => by
      rw [List.mem_singleton] at he'; rw [he', hpc]; unfold w0ArrSPc w0ArrLPc; omega)
  have hext := w0Words_ext (w0Fin ((X.tr g).take k)).2 [e] (fun e' he' => by
    rw [List.mem_singleton] at he'; rw [he', hpc]; omega)
  have hpmx : (w0Words ((w0Fin ((X.tr g).take k)).2 ++ [e])).pm =
      (w0Words (w0Fin ((X.tr g).take k)).2).pm := by
    simp only [w0Words]
    exact congrArg (·.getD (Value.pred false)) (w0Last_ext _ [572] _ _ (fun e' he' => by
      rw [List.mem_singleton] at he'; rw [he', hpc]; simp))
  have hmem : e ∈ (w0Fin ((X.tr g).take (k + 1))).2 := by
    rw [hfin]; exact List.mem_append_right _ (List.mem_singleton_self e)
  have hnow := (hv.now).2 ⟨e, hmem, hpc⟩
  rw [hfin] at hnow
  obtain ⟨hlo, hhi, hmw, hpw⟩ := hext
  have hw0 : W0Ok P.scale (w0Words (w0Fin ((X.tr g).take k)).2) := by
    refine ⟨hnow.scale, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hhi]; exact hnow.hiLen
    · intro c hc; rw [← hhi]; exact hnow.hi c hc
    · rw [← hlo]; exact hnow.loLen
    · intro c hc; rw [← hlo]; exact hnow.lo c hc
    · rw [← hmw]; exact hnow.mask
    · intro j hj; rw [← hpw j]; exact hnow.peer j hj
    · rw [← hpmx]; exact hnow.pm
  obtain ⟨hbhi, hbmw, hbpw, hbpm⟩ : d.b.hi = (w0Words (w0Fin ((X.tr g).take k)).2).hi ∧
      d.b.mw = (w0Words (w0Fin ((X.tr g).take k)).2).mw ∧
      (∀ j, d.b.pw j = (w0Words (w0Fin ((X.tr g).take k)).2).pw j) ∧
      d.b.pm = (w0Words (w0Fin ((X.tr g).take k)).2).pm := by
    rw [w0Fin_snd]
    exact ⟨hIW.hi, hIW.mw, hIW.pw, hIW.pm⟩
  obtain ⟨-, hsub, -, -, hF⟩ := hat
  change Holds t.regs (_ ++ dF L d) at hF
  have hF' := ((holds_append _ _ _).mp hF).2
  have hdF : dF L d = f_vote (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) d.b.pm := by
    unfold dF
    simp only [hok, ↓reduceIte]
    unfold wF wcls
    rw [hsite]
    rfl
  rw [hdF] at hF'
  have hmem : 109 ∈ (f_vote (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7)
      d.b.pm).map Prod.fst := by
    unfold f_vote
    rw [List.map_append]
    exact List.mem_append_left _ (by simp only [Gen.mld_facts1, List.map_cons, List.map_nil]; simp)
  have hreg := holds_of_mem hF' hmem
  rw [w0_vote_pred hw0 hx hbhi hbmw hbpw hbpm hm hl hmx] at hreg
  change kernel.code[d.c.site.pc]? = _ at hcode
  rw [hsite, show Site.pc .vote = 578 from rfl, Flow.code_578] at hcode
  cases hcode
  obtain ⟨m', r', hev⟩ := fires_voteAnyU_in hub hreg hf
  obtain ⟨pc', kd⟩ := e
  simp only [Event.mk.injEq] at hev hk
  rw [hev.2] at hk
  simp only [Kind.voteMode.injEq] at hk
  rw [← hk.2.2.1]
  simp [w0VoteIn, w0VoteArg]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
