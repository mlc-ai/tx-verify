-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Ord
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Won
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.Winner
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BarOrd
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.Faults

@[expose] public section

/-! # The inputs: the rows the roles owe, in one bundle

`Top.Inputs P L m` carries to the progress and the safety classes the trace-level rows of the
roles. It has no field left: `Inputs.of_pre` proves it from `Pre`. The full bundles the classes
consume (`MbarRows`, `BarRows`, `RawInputs`, `CoordInputs`,
`WaitRows`, `QueryTime`) are assembled below (`Inputs.mbar`, `Inputs.bar`, `Inputs.raw`,
`Inputs.coord`, `Inputs.wait`, `Inputs.query`) from `Pre`, the following premise of the
execution and the roles' export lemmas.

The dequantized buffer ring's rows are proved: `Inputs.dequant` (the MMA lane's commits,
`mma_svArr`) and `Inputs.drTime` (`DrTime`: `mma_drWait`, `deq_drEarly`, `deq_drExit`).

The mbarrier records' fault freedom (ERR-OBJECT-LIFETIME, `Safe.noTma`) is proved: `Inputs.faults`
(`Protocol/Mbar/Faults.lean`); so is the footprints' disjointness from the mbarriers
(`Safe.threadBytes`, `Safe.asyncBytes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow PTX.MbarRing

/-- **The rows the roles owe**: none are left, so the structure has no field (`Inputs.of_pre`);
the safety and progress classes still take it as the carrier of the assembled bundles below. -/
structure Inputs (P : Params) (L : Launch) (m : Mem0) : Prop

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The inputs hold** under `Pre`: every row is a role's export (assembled below). -/
theorem Inputs.of_pre (_hp : Pre P L m) : Inputs P L m := ⟨⟩

/-- **The mbarrier rows of every role**, from the roles' exports. -/
theorem Inputs.mbar (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : MbarRows P L X :=
  ⟨mbarRow_startup hp hX hFw, mbarRow_wg1 hp hX hFw, mbarRow_mma hp hX hFw,
    mbarRow_tma hp hX hFw, mbarRow_index hp hX hFw, mbarRow_dequant hp hX hFw,
    mbarRow_wg0 hp hX hFw, mbarRow_place hp hX hFw⟩

/-- **The named-barrier rows of every role**, from the roles' exports. -/
theorem Inputs.bar (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : BarRows P L X :=
  ⟨barRow_startup hp hX hFw, barRow_wg0 hp hX hFw, barRow_wg1 hp hX hFw, barRow_mma hp hX hFw,
    barRow_tma hp hX hFw, barRow_index hp hX hFw, barRow_dequant hp hX hFw,
    barRow_place hp hX hFw⟩

/-- The TMA thread of CTA `c` is a lane of warp 5 of the CTA. -/
private theorem tmaThread_warp (hp : Pre P L m) (X : Execution) (c : Nat) :
    MbarRow.warp L (tmaThread L X c) = 5 ∧ tmaThread L X c / L.block = c := by
  have h := tmaThread_mod (X := X) hp c
  simp only [MbarRow.warp, tidOf_x_eq hp, hp.block]
  omega

/-- **The raw ring's counts**: the TMA lane's (`tmaOne`, `tma_rawArr`, `tma_rawIss`) and the
dequant lanes' arrivals (`dequant_freeArr`). -/
theorem Inputs.raw (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : RawInputs L X :=
  ⟨tmaOne hp hX hFw,
    fun he => tma_rawArr hp hX hFw (tmaThread_warp hp X _).1 (tmaThread_warp hp X _).2 he,
    fun he hm => tma_rawIss hp hX hFw (tmaThread_warp hp X _).1 (tmaThread_warp hp X _).2 he hm,
    fun {c _ _ _ b _} he => dequant_freeArr hp hX hFw
    (by have hb := b.isLt; simp only [MbarRow.warp, deqLane, tidOf_x_eq hp, hp.block]; omega) he⟩

/-- **The coordination ring's counts**: the index lanes', warpgroup 0's and the TMA lane's
arrivals from `index_idxArr`, `wg0_coordArr` and `tma_coordArr`. -/
theorem Inputs.coord (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : CoordInputs L X :=
  ⟨tmaOne hp hX hFw, fun he => index_idxArr hp hX hFw he,
    fun hb he => wg0_coordArr hp hX hFw hb he,
    fun he => tma_coordArr hp hX hFw (tmaThread_warp hp X _).1 (tmaThread_warp hp X _).2 he⟩

/-- **The wait-step rows**: warpgroup 0's, the TMA lane's, the index warp's and the dequant
lanes' from `wg0_waitRow`, `tma_waitRow`, `index_waitRow`, `dequant_waitRow`. -/
theorem Inputs.wait (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (_hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : WaitRows P L m X :=
  ⟨wg0_waitRow hp hFw, tma_waitRow hp hFw, index_waitRow hp hFw, dequant_waitRow hp hFw⟩

/-- **The `qUtccp` waiters' slot facts**: the TMA lane's from `tma_query_slot`, the dequant
lanes' from `dequant_slot_wait`. -/
theorem Inputs.query (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (_hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : QueryTime P L m X :=
  ⟨fun hat hn => tma_query_slot hp hFw hat hn, fun hd hn => (dequant_slot_wait hp hFw hd hn).ge⟩

/-- **The barrier-0 rows** (`Protocol/Mbar/Bar0.lean`): the count from the barrier rows
(`bar0_count`), the exit from `bar0_exit`. -/
theorem Inputs.bar0 (hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : Bar0Rows L X :=
  ⟨fun ha hg => bar0_count (hIn.bar hp X hX hFw) ha hg, fun _ he => bar0_exit hp hX hFw he⟩

/-- **The barrier ordinals**: the startup's barrier first and every later one after a barrier
(`bar_first`, `bar_later`), warpgroup 0's lanes of one warp at one ordinal at one pc
(`barOrd_wg0`). -/
theorem Inputs.barOrd (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : BarInputs L X :=
  ⟨bar_first hp hX hFw, fun _ he hpc hb => bar_later hp hX hFw he hpc hb,
    fun hs he he' ha ha' hb hb' hc => barOrd_wg0 hp hX hFw hs he he' ha ha' hb hb' hc⟩

/-- **The startup's initialization rows**: `won` from the startup's history
(`startup_init_won`; an initialization is the startup's, `mbar_use`), `winner` from the
barrier-0 rows (`init_winner`). -/
theorem Inputs.initRows (hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : InitRows L X where
  won := by
    intro g k n e l hg he hk
    have hm : Frame.MbarOf e l := by
      obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      rfl
    rcases mbar_use (hIn.mbar hp X hX hFw) hg he hm with ⟨hw, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ |
      ⟨-, h⟩ | ⟨-, h⟩
    · exact startup_init_won hp hX hFw hg he hk hw
    all_goals
      cases h <;> simp_all [MbarRow.Wait, MbarRow.Arrive, MbarRow.Commit, MbarRow.Issue]
  winner := fun {h f} hh hpass hpos =>
    init_winner hp hX hFw (hIn.bar0 hp X hX hFw) hh hpass hpos

/-- **The dequantized buffer ring's commit row**: the MMA lane's commit of use `u` to `svDone s`
follows `u + 1` successful polls of `dequantReady s` (`mma_svArr`; the lane committing is of
warp 4, `mma_commit_warp`). -/
theorem Inputs.dequant (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : DequantInputs L X :=
  ⟨fun he hm => mma_svArr hp hX hFw (mma_commit_warp hp hX hFw he) he hm⟩

/-- **The time facts of the dequantized buffer ring** (`DrTime`): the MMA lane's wait
(`mma_drWait`), the dequant lanes' arrivals (`deq_drEarly`) and exit (`deq_drExit`). -/
theorem Inputs.drTime (_hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : DrTime P L m X :=
  ⟨fun hn => mma_drWait hp hX hFw hn,
    fun hub {c a _} hy hlt =>
      deq_drEarly hp hX hFw hub (deqLane_warp hp c a) hy (deqLane_cta hp c a) hlt,
    fun {c _ _ a _} hx => deq_drExit hp hX hFw (deqLane_warp hp c a) (deqLane_cta hp c a) hx⟩

/-- **No record of an mbarrier object faults** (the objects of every family and CTA,
`mbar_fault`), from the rows of the roles. -/
theorem Inputs.faults (hIn : Inputs P L m) (hp : Pre P L m) (X : Execution)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) (c : Nat) (f : MbarFam) :
    ∀ r ∈ X.objects (mbarLoc L c f), r.fault = none :=
  mbar_fault hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw)
    (hIn.dequant hp X hX hFw) (hIn.raw hp X hX hFw) (hIn.coord hp X hX hFw) c f

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
