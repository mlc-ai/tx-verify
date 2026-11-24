-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.AssembleBase
public import Kernels.InklingRelDecode.Proof.AssembleLk4
public import Kernels.InklingRelDecode.Proof.Progress.All
public import Kernels.InklingRelDecode.Proof.Progress.WtAll
public import Kernels.InklingRelDecode.Proof.Progress.WfBarAll
public import Kernels.InklingRelDecode.Proof.Progress.WuAll
public import Kernels.InklingRelDecode.Proof.Progress.LibAll
public import Kernels.InklingRelDecode.Proof.Progress.WxAll
public import Kernels.InklingRelDecode.Proof.Progress.WyAll
public import Kernels.InklingRelDecode.Proof.Progress.WvAll
public import Kernels.InklingRelDecode.Proof.Progress.WkAll
public import Kernels.InklingRelDecode.Proof.Progress.WmAll
public import Kernels.InklingRelDecode.Proof.Progress.WnAll
public import Kernels.InklingRelDecode.Proof.Progress.WqLag
public import Kernels.InklingRelDecode.Proof.Protocol.VxAll
public import Kernels.InklingRelDecode.Proof2.Safety.Tmem
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmAlloc
public import Kernels.InklingRelDecode.Proof.Protocol.WzAll
public import Kernels.InklingRelDecode.Proof.Result.WzAll
public import Kernels.InklingRelDecode.Proof.AssembleLock
public import Kernels.InklingRelDecode.Proof.Protocol.HsAll
public import Kernels.InklingRelDecode.Proof.Protocol.VxAll
public import Lemmas.Order.Order
public import Kernels.InklingRelDecode.Proof.Safety.All
public import Lemmas.Protocol.RegionOrderExcept

@[expose] public section

/-!
# `Progress.Remaining` from the proved progress theorems

Every field of `Progress.Remaining` has a proof (`remaining_of`):

* `time := Wt.time`, `wait_time := Wt.wait_time`;
* `reads`: `ConflictsOrderedExcept.readsOrdered` from the ordered conflicts of the safety layer
  (`Safety.conflicts_ordered_of`, with `Safety.Protocol`): the same-value write pairs need no
  order;
* `regWaits`: `exit` is `Wt.reg_exit` (from `¬ Unsafe`, supplied by `safe_goal`), `after` is
  `Wt.reg_after`, `before` is `Wu.reg_before`;
* `tcWaits`: `after` is `Wt.tc_after`, `lag` is `Wx.tcLag_of` (with `hD`);
* `regIssue := regIssue_of`; `tmemSteps := tmemSteps_of` (with `Proof2.tmem1Facts` and `tcWaits`);
* `fresh := Interface.readFresh_of` (a read at a site of the read-only input assumption reads
  input bytes, which no write covers);
* `barSteps := barSteps_of` with `Bar0Facts` from `Wt.bar0Facts_of` (premise: `Bar.AlphaAgree`,
  shared with `Safety.Protocol.ctaBar`) and `BarTime` (`after` is `Wt.bar_after`, `lag1`, `lag0e`,
  `lag0f` are `Wu.bar_lag1`, `Wu.bar_lag0e`, `Wu.bar_lag0f`, `lag0l` is `Wx.lag0l_of` with the
  agreement of the lazy-rescale decisions `hD`, from the scratch words `hI`).

* `warpColl` (in a maximal execution): `WarpCollFacts.exit` is `Progress.Lk4.warpColl_exit`,
  `shape` is `Progress.Wn.warpColl_shape`, `last` is `Progress.Wn.warpColl_last` (the warp
  lockstep, from `Base.laneAgree`) and `lag` is `Progress.Wq.lag_of` (the key time `Lk.kx` at one
  synchronizing ordinal, `Lk.kx_lock`, and along a trace, `Wq.kx_mono`).

* `async`: `ATmemApart` and `LayoutInjective` are `Wx.aTmemApart_of` and `Wx.layoutInjective_of`
  (the two MMA shapes); `TensorSources` is `Wz.tensorSources_of` and `OperandSourcesT` is
  `Wz.operandSources_of` (both on every consistent execution), the latter from `Wz.qTileF_of`,
  `Wz.kvCopiesF_of` and the handshake package (`Hs.pkg_of`, with the scratch words `hI`).

* `polls`: `Wy.pollsBlocked_of`: the next event of the thread (`Wy.poll_next`) and the polled
  object's final state (`Wy.pollAt_final`) are proved; the blocker clause is `Wy.pollsRest_of`:
  for the default partition's polls (`s_ready`, `o_done`, `o_final`) and the MMA warp's `p_ready`
  poll the protocol part is proved with the handshake package (`Hs.pkg_of`, built here from the
  scratch words `hI`); the lag of the producer and the parity of the MMA warp's polls at its end
  state are `Wv.cmLag_of`, `Wv.p0Lag_of`, `Wv.mmaParity_of`; the KV ring's polls are
  `Wk.workerPollsRest_of`: the loader's `kv_empty` poll is proved for every lane of the loader
  warp, the MMA warp's `kv_ready` poll is `Wm.mmaKvPollsRest_of` for the blocks after the
  preloaded ones, and `Wn.mmaKvPre_of` for the preloaded blocks.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Assemble
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Progress.Remaining`** from the safety result, the thread-layer base, the safety layer's
protocol facts and `Bar.AlphaAgree`. -/
def remaining_of (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hbase : ∀ X, Consistent L kernel asms mem0 X → Base Q L mem0 X)
    (hprot : ∀ X, Consistent L kernel asms mem0 X → Safety.Protocol Q L X)
    (halpha : ∀ X, Consistent L kernel asms mem0 X → Bar.AlphaAgree L X)
    (hsm : ∀ X, Consistent L kernel asms mem0 X → Interface.Lk.LaneAgreeSm Q L X)
    (hI : ∀ X, Consistent L kernel asms mem0 X → ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Remaining Q L mem0 :=
  have hD : ∀ X, Consistent L kernel asms mem0 X → ∀ c j, Interface.Lk.DecAgree Q L X c j :=
    fun X hX => Interface.Lk.decAgree_every hpre hX (hbase X hX).facts (hI X hX)
  have hS : ∀ g < L.threads, (threadCode L g Q).Sound := Interface.sound_all hpre Interface.smOb
  have htr : ∀ X, Consistent L kernel asms mem0 X → Frame.Tracked (code L Q) X :=
    fun X hX => (hbase X hX).facts.tracked
  have hRR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X :=
    fun _ hX => Base.roleReads hpre hX
  have hw : ∀ X, Consistent L kernel asms mem0 X → Sched.TcWaitFacts (timed Wt.time Q L) X :=
    fun X hX => ⟨fun hg hh hsw hK hσ hle => Wx.tcLag_of hpre hX (hbase X hX).facts
        (Sched.safe_noUb (hs.2 X hX)) (hD X hX) hg hh hsw hK hσ hle,
      fun hg hk hσ => Wt.tc_after hpre (hRR X hX) hX hS (htr X hX) hg hk hσ⟩
  { time := Wt.time
    wait_time := Wt.wait_time
    reads := fun X hX => (Safety.conflicts_ordered_of hpre Interface.smOb hX (hbase X hX).prem
      (hprot X hX)).readsOrdered
    async :=
      { tensor := fun X hmax =>
          Wz.tensorSources_of hpre hmax.1 (hbase X hmax.1).facts
            (Base.numWordRead hpre hmax.1)
        mma := fun X hmax =>
          have b := hbase X hmax.1
          have G := Hs.pkg_of hpre hmax.1 b.facts (Base.roleReads hpre hmax.1)
            (Interface.baseWordRead_of hpre hmax.1)
            (Base.numWordRead hpre hmax.1) (hI X hmax.1)
            (Vx.pkgRest_of hpre hmax.1 b.facts (Base.roleReads hpre hmax.1)
              (Base.mmaBcast hpre hmax.1 b))
          ⟨Wz.operandSources_of hpre hmax.1 b.facts b.tmpl (Base.roleReads hpre hmax.1) b.bar1
            (Base.numPreRead hpre hmax.1) (Base.boxInBounds hpre hmax.1) G
            (Base.mmaBcast hpre hmax.1 b)
            (Wz.qTileF_of hpre hmax.1 b.facts b.tmpl (Base.roleReads hpre hmax.1) b.bar1)
            (Wz.kvCopiesF_of hpre hmax.1 b.facts (Base.roleReads hpre hmax.1)
              (Base.numPreRead hpre hmax.1) G),
            Wx.aTmemApart_of hpre hmax.1 b.facts (Interface.baseWordRead_of hpre hmax.1)
              (Base.numWordRead hpre hmax.1),
            Wx.layoutInjective_of hpre hmax.1 b.facts (Interface.baseWordRead_of hpre hmax.1)
              (Base.numWordRead hpre hmax.1)⟩ }
    polls := Wy.pollsBlocked_of hpre hS (fun X hX => (hbase X hX).facts) hRR
      (fun X hX => Sched.safe_noUb (hs.2 X hX))
      (Wy.pollsRest_of hpre (fun X hX => (hbase X hX).facts) hRR
        (fun X hX => Sched.safe_noUb (hs.2 X hX))
        (fun X hX => ⟨Hs.pkg_of hpre hX (hbase X hX).facts (hRR X hX)
          (Interface.baseWordRead_of hpre hX)
          (Base.numWordRead hpre hX) (hI X hX)
          (Vx.pkgRest_of hpre hX (hbase X hX).facts (hRR X hX)
            (Base.mmaBcast hpre hX (hbase X hX))), fun _ => rfl, fun _ => rfl,
          fun _ _ h => h⟩)
        (Wv.cmLag_of hpre (fun X hX => (hbase X hX).facts) hRR
          (fun _ hX => Interface.baseWordRead_of hpre hX)
          (fun _ hX => Base.numWordRead hpre hX)
          (fun X hX => Base.mmaBcast hpre hX (hbase X hX)))
        (Wv.mmaParity_of hpre (fun X hX => (hbase X hX).facts) hRR)
        (Wv.p0Lag_of hpre (fun X hX => (hbase X hX).facts) hRR
          (fun _ hX => Interface.baseWordRead_of hpre hX)
          (fun _ hX => Base.numWordRead hpre hX))
        (Progress.Wk.workerPollsRest_of hpre (fun X hX => (hbase X hX).facts) hRR
          (fun _ hX => Interface.baseWordRead_of hpre hX)
          (fun _ hX => Base.numWordRead hpre hX)
          (fun _ hX => Base.numPreRead hpre hX)
          (fun X hX => Base.mmaBcast hpre hX (hbase X hX))
          (fun X hX => Sched.safe_noUb (hs.2 X hX))
          (fun X hX => ⟨Hs.pkg_of hpre hX (hbase X hX).facts (hRR X hX)
            (Interface.baseWordRead_of hpre hX)
            (Base.numWordRead hpre hX) (hI X hX)
            (Vx.pkgRest_of hpre hX (hbase X hX).facts (hRR X hX)
            (Base.mmaBcast hpre hX (hbase X hX))), fun _ => rfl⟩)
          (Progress.Wm.mmaKvPollsRest_of hpre (fun X hX => (hbase X hX).facts) hRR
            (fun _ hX => Interface.baseWordRead_of hpre hX)
            (fun _ hX => Base.numWordRead hpre hX)
            (fun _ hX => Base.numPreRead hpre hX)
            (fun X hX => Sched.safe_noUb (hs.2 X hX))
            (fun X hX => ⟨Hs.pkg_of hpre hX (hbase X hX).facts (hRR X hX)
              (Interface.baseWordRead_of hpre hX)
              (Base.numWordRead hpre hX) (hI X hX)
              (Vx.pkgRest_of hpre hX (hbase X hX).facts (hRR X hX)
            (Base.mmaBcast hpre hX (hbase X hX))), fun _ => rfl⟩)
            (Progress.Wn.mmaKvPre_of hpre (fun X hX => (hbase X hX).facts) hRR
              (fun _ hX => Base.numPreRead hpre hX)
              (fun X hX => Sched.safe_noUb (hs.2 X hX))
              (fun X hX => ⟨Hs.pkg_of hpre hX (hbase X hX).facts (hRR X hX)
                (Interface.baseWordRead_of hpre hX)
                (Base.numWordRead hpre hX) (hI X hX)
                (Vx.pkgRest_of hpre hX (hbase X hX).facts (hRR X hX)
            (Base.mmaBcast hpre hX (hbase X hX))), fun _ => rfl⟩)))))
    warpColl := fun X hmax =>
      have hX := hmax.1
      { shape := Progress.Wn.warpColl_shape hX (hbase X hX).facts
          (Base.laneAgree hpre hX (hbase X hX) (hsm X hX))
        last := Progress.Wn.warpColl_last hpre hX (hbase X hX).facts
          (Base.laneAgree hpre hX (hbase X hX) (hsm X hX))
        exit := Progress.Lk4.warpColl_exit hX (hbase X hX).facts
          (Base.laneAgree hpre hX (hbase X hX) (hsm X hX))
        lag := fun hg hh hw hσ hk hrel hle hno => Progress.Wq.lag_of hpre hmax
          (hbase X hX).facts (Base.laneAgree hpre hX (hbase X hX) (hsm X hX))
          (Base.roleReads hpre hX) (Base.numPreRead hpre hX)
          (Sched.safe_noUb (hs.2 X hX)) hg hh hw hσ hk hrel hle hno }
    regWaits := fun X hX =>
      { exit := Wt.reg_exit (hs.2 X hX)
        before := fun hg hh hw hno hget hσ => Wu.reg_before hpre hX hS (htr X hX) (hRR X hX)
          (Sched.safe_noUb (hs.2 X hX)) hg hh hw hno hget hσ
        after := fun hg he hσ => Wt.reg_after hpre (hRR X hX) hX hS (htr X hX) hg he hσ }
    tcWaits := hw
    regIssue := regIssue_of hS hs
    barSteps := barSteps_of hpre hs hS htr
      (fun X hX => Wt.bar0Facts_of hpre hX hS (htr X hX) (hs.2 X hX) (halpha X hX))
      (fun X hX =>
        { after := fun hg he hσ => Wt.bar_after hpre (hRR X hX) hX hS (htr X hX) hg he hσ
          lag1 := fun hg hget hσ hy hdiv hle => Wu.bar_lag1 hpre hX hS (htr X hX) (hRR X hX)
            (Sched.safe_noUb (hs.2 X hX)) hg hget hσ hy hdiv hle
          lag0e := fun hg hget hm hσ hy hdiv hle => Wu.bar_lag0e hX hS (htr X hX)
            (Sched.safe_noUb (hs.2 X hX)) hg hget hm hσ hy hdiv hle
          lag0l := fun hg hget hσ hy hc hyd hle => Wx.lag0l_of hpre hX (hbase X hX).facts
            (Sched.safe_noUb (hs.2 X hX)) (hD X hX) hg hget hσ hy hc hyd hle
          lag0f := fun hg hget hm hσ hy hdiv hno => Wu.bar_lag0f hpre hX hS (htr X hX)
            (hRR X hX) (Sched.safe_noUb (hs.2 X hX)) hg hget hm hσ hy hdiv hno })
    tmemSteps := tmemSteps_of hpre hs hS htr
      (fun _ hX => Proof2.tmem1Facts hpre hX) hw
    fresh := fun X hX => Interface.readFresh_of hpre hX (hbase X hX).facts
      (Base.numWordRead hpre hX) }

end
end PTX.Kernels.InklingRelDecode.Proof.Assemble
