-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietAlloc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Next
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.NextEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NextAll
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.CollRel
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.VoteRel
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Group
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe

@[expose] public section

/-! # A released lane steps, or has a next event

`Prog.nextRow`: the `next` row of the progress classes (`NextRow.Next`). A pending released lane
of a maximal execution of a safe launch steps, or its trace extends consistently by an event that
is no undefined behaviour (`next_all`, `Common/Export/NextAll.lean`), given what the lane's
instruction needs of the execution: its facts (`Prog.nextEnv`), every lane's drained stores
(`Prog.drained`), the warp facts (`coll_rel`, `vote_rel`, from every barrier's participant group,
`bar_group`), the allocations at column 0 (`Prog.allocZero`) and the final state of every
mbarrier of the lane's CTA once it has passed barrier 0 (`objects_final`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **A pending released lane steps or has a next event.** -/
theorem Prog.nextRow (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Next P L m X := by
  intro hs hmax g hpd hrel
  have hX := hmax.1
  have hFw := follow_of hp X hX
  have hnu := Sched.safe_noUb (hs.2 X hX)
  have hR := hIn.bar hp X hX hFw
  have hgrp : ∀ {g i pc id : Nat} {cnt : Option Nat} {md : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt md⟩ →
      ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id :=
    fun hg he => by
      obtain ⟨q, h1, h2, -⟩ := bar_group hp hR hg he
      exact ⟨q, h1, h2⟩
  exact next_all hp (Prog.nextEnv hp hs hmax) hs hFw (fun h => Prog.drained hp hpub hs hmax h)
    (coll_rel hp hX hFw hnu hgrp) (vote_rel hp hX hFw hnu hgrp)
    (fun hr n col hact => Prog.allocZero hIn hp hX hFw hr n col hact)
    (fun f hb => by
      rw [← List.take_length (l := X.tr g)] at hb
      exact objects_final hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
        (hIn.bar0 hp X hX hFw) hpd.1 (.inr ⟨rfl, hrel⟩) hb f)
    hpd hrel

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
