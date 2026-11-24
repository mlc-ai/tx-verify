-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeExit
public import Kernels.InklingRelDecode.Proof.Protocol.TmemAccess
public import Lemmas.Kernel.ExitChain

@[expose] public section

/-!
# An MMA finishes before its CTA exits

`Life.MmaFinished` (`IpLifeUse`): the completion of an MMA precedes an exit of its CTA once the
CTA exited. The kernel's MMAs all precede the MMA warp's one commit to `o_final`, which tracks them
(`TracksMma`: a commit tracks every earlier MMA of its thread), and the commit's notification is
observed by the epilogue's poll of `o_final` in every default-partition thread, also when
`num_iters = 0` (the second kernel fix). So:

* `f_observed`: the epilogue's poll of `o_final` observes, for every MMA of its CTA, the completion
  of that MMA through the commit's notification (the observation `SO.f_doneBefore_at` builds,
  without its causality conclusion);
* `mmaFinished`: lane 0 of warp 0 of an exited CTA exits after such a poll (`exit_poll`), which is
  a canonical spin, so its exit resumes from the poll in the dependency order
  (`Resumes.of_spin`); the completion of the MMA precedes the poll's return
  (`CompletedBefore.of_observesMma`) and so the exit.

Premises: `Tmem1.OFinalFacts` for every launched CTA `c < L.grid` (the MMA warp `cm` of the CTA,
its only commit to `o_final`, that every MMA of the CTA is `cm`'s and precedes that commit): the
thread layer's row
"Protocol `Tmem`: `OFinalFacts`" of the gap table, shared with `tmemAccess`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier TcMma
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX.Kernels.InklingRelDecode.Proof.EvW (oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma fObj fReach)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {c cm p0 : Nat}

/-- **The epilogue's poll of `o_final` observes the completion of every MMA of its CTA.** -/
theorem f_observed (hX : Consistent L kernel asms mem0 X) (F : SO.Facts L X c cm p0)
    (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm)
    (hcommit : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFinal L c →
        ((X.tr cm).take i).countP (commitsTo (oFinal L c)) = 0)
    (hbefore : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFinal L c → x.2 < i)
    {h j pc p : Nat} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (oFinal L c) p true true sc⟩) {x : EvId}
    (hx : IsMma X x) (hxc : x.1 / L.block = c) :
    ∃ ws, AsyncCopy.AsyncObserved X x .mmaDone (h, j) true ws := by
  have hq : okPolls (oFinal L c) ((X.tr h).take j) + 0 = okPolls (oFinal L c) ((X.tr h).take j) :=
    rfl
  obtain ⟨i, pcx, sp, rank, hget, hmbar, htgt, hcnt, hrank, hobs⟩ :=
    (SO.fObj hX F).observes hX (fReach hX F h hcommit) he hq
  have hthr : x.1 = cm := hone hx hxc
  have hlt : x.2 < i := hbefore hx hxc hget hmbar
  exact ⟨sc, .async (cm, i) (.tcNotify rank), oFinal L c,
    ⟨(cm, i), sp, rank, rfl, ⟨hthr.symm ▸ rfl, hlt, .inl hx, sp, pcx, hget⟩, ⟨pcx, hget⟩, htgt,
      hrank⟩, hobs⟩

/-- **`MmaFinished`**: the completion of an MMA precedes an exit of its CTA, once the CTA exited. -/
theorem mmaFinished (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (F : ∀ c < L.grid, Tmem1.OFinalFacts L X c) :
    MmaFinished L X := by
  intro i d s acc mask c hmi hlh hx
  obtain ⟨h1, h2⟩ := mma_own_of hpre hX hf hmi
  have hown : c = i.1 / L.block := by rcases hlh with rfl | rfl <;> assumption
  obtain ⟨pci, hgeti⟩ := hmi
  have hig := Frame.lt_of_get hX hgeti
  have hc : c < L.grid := by rw [hown]; exact cta_lt_grid hpre hig
  have hb : L.block = 256 := hpre.block
  have hh : c * L.block < L.threads := by
    unfold Launch.threads
    exact Nat.mul_lt_mul_of_pos_right hc (by omega)
  have hhc : c * L.block / L.block = c := Nat.mul_div_cancel c (by omega)
  have hhd : c * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
  obtain ⟨pc, hl⟩ := hx (c * L.block) hh hhc
  rw [List.getLast?_eq_getElem?] at hl
  obtain ⟨cm, p0, Fa, hcm, hcmc, hone, hcommit, hbefore⟩ := F c hc
  have hkh : X.get (c * L.block, (X.tr (c * L.block)).length - 1) = some ⟨pc, .exit⟩ := hl
  obtain ⟨j, hjk, pc', p, sc, hget⟩ := exit_poll hpre hX hf hkh hhd
  rw [hhc] at hget
  obtain ⟨ws, hobs⟩ := f_observed hX Fa hone hcommit hbefore hget ⟨_, _, _, _, ⟨pci, hgeti⟩⟩
    hown.symm
  obtain ⟨ex, hsp⟩ := poll_spins hX (show X.get (c * L.block, j) = _ from
    (hhc ▸ hget : X.get (c * L.block, j) = some ⟨pc', .wait (oFinal L c) p true true sc⟩))
  have hres : Resumes kernel X (c * L.block, j) (c * L.block, (X.tr (c * L.block)).length - 1) :=
    Resumes.of_spin hget hsp rfl hjk (len_of_get hkh)
  obtain ⟨hd, hcb⟩ := CompletedBefore.of_observesMma hX.tcCommit hobs
    (.single (DepStep.of_resumes L hres))
  exact SharedFinished.of_completedBefore (finish := (c * L.block, (X.tr (c * L.block)).length - 1))
    hd ⟨hh, hhc, pc, hkh⟩ hcb

end
end PTX.Kernels.InklingRelDecode.Proof.Life
