-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Life.Exit
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Mma.Export.FinalCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Kernel.SharedLifetime

@[expose] public section

/-! # An MMA finishes before its CTA exits

Every MMA of a CTA is before the CTA's one final commit, which tracks it (`TracksMma`). The final
commit's arrival is observed by the poll of `o_final` that every default lane makes before its
exit (`exit_poll`, `Tmem.poll_observes`). The poll is a canonical spin that resumes the lane's
exit, so the MMA's completion precedes the exit. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX PTX.Flow PTX.AsyncCopy PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem issue_pc {pc : Nat}
    (h : (∃ j : Fin 8, pc = Lib.qkIssue j) ∨ ∃ j : Fin 8, pc = Lib.pvIssue j) :
    pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498,2530,2533,2535,2537,2539,2541,2543,2545] := by
  rcases h with ⟨j,h⟩ | ⟨j,h⟩ <;> subst h <;> fin_cases j <;> decide

/-- **`MmaFinished`**: the completion of an MMA precedes an exit of its CTA, once the CTA exited. -/
theorem mma_finished (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (base : Iface.BaseRead L X) : MmaFinished L kernel Assumptions.all X := by
  intro i d s acc mask hmi hx
  obtain ⟨y0, i0⟩ := i
  obtain ⟨pc0, he⟩ := hmi
  have hg := Frame.lt_of_get hX he
  have hc : y0 / L.block < L.grid :=
    Nat.div_lt_of_lt_mul (by simpa [Launch.threads, Nat.mul_comm] using hg)
  have hcd : y0 / L.block * L.block / L.block = y0 / L.block :=
    Nat.mul_div_cancel _ (by rw [hp.block]; omega)
  obtain ⟨jw, kx, l, q, ac, sc, hjk, hown, hpoll⟩ := final_wait hp hX hf hc hx
  obtain ⟨-, -, pcx, hkh⟩ := id hown
  obtain ⟨ic, spi, rank, hgc, hti, hrk, hobs⟩ := Tmem.poll_observes hp hX hf rows init hpoll
  obtain ⟨lead, -⟩ := Tmem.mma_leader hp hX hf he
  rw [hcd, lead] at hgc hrk hobs
  rw [hcd] at hti
  obtain ⟨-, -, -, bb, hcol⟩ := Mma.Export.columns hp hX hf (fun h1 h2 h3 => base h1 h2 h3) he
  have issue := issue_pc (by
    rcases hcol with ⟨j,h,-⟩ | ⟨j,h,-⟩ <;> [exact .inl ⟨j,h⟩; exact .inr ⟨j,h⟩])
  have hj := Mma.Export.mma_before_final hp hX hf (fun h => Protocol.Shared.role_bytes hp hX h)
    hgc he issue
  have htr : TracksMma X (y0,i0) (y0,ic) := ⟨rfl, hj, .inl ⟨d,s,acc,mask,pc0,he⟩, spi, 2553, hgc⟩
  have hobs' : AsyncObserved X (y0,i0) .mmaDone (_, jw) true .cta :=
    ⟨_, _, ⟨(y0,ic), spi, rank, rfl, htr, ⟨2553, hgc⟩, hti, hrk⟩, hobs⟩
  obtain ⟨ex, hsp⟩ := (Lib.poll_site hX hpoll).2
  have hres : Resumes kernel X (_, jw) (_, kx) :=
    Resumes.of_spin hpoll hsp rfl hjk (len_of_get hkh)
  obtain ⟨hd, hcb⟩ := CompletedBefore.of_observesMma hX.tcCommit hobs'
    (.single (DepStep.of_resumes L hres))
  exact SharedFinished.of_completedBefore hd hown hcb

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
