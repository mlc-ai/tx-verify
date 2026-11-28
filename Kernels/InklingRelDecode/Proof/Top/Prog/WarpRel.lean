-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
public import Kernels.InklingRelDecode.Proof.Top.Prog.BlockAny
public import Kernels.InklingRelDecode.Proof.Common.Export.WarpPairs
import Kernels.InklingRelDecode.Proof.Top.Prog.Mate
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Kernels.InklingRelDecode.Proof.Top.Prog.CollSteps
import Kernels.InklingRelDecode.Proof.Top.Prog.TmemBlocked
import Kernels.InklingRelDecode.Proof.Common.Export.BarClock
import Kernels.InklingRelDecode.Proof.Common.Export.BarEarly
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Bar.LoopLag
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Progress.WarpReady

/-! # A stopped lane and a mate of a released lane are released

The facts of the lanes of a warp at a warp collective that the progress step needs beyond the
collectives themselves. A machine does not stop after a blocking event, so a pending lane whose
machine stopped has a released last event. A lane that is blocked at a collective's predecessor
(`Lib.pairs`) while a lane of its warp at the collective is released is not blocked. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Frame

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A pending lane whose machine stopped is released.** -/
public theorem Prog.warp_dead (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hm : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) {P : Nat → Prop} :
    WarpDead Q L X P := by
  intro y _ hpd hgone
  by_contra hr
  have hX := hm.1
  have nu : NoUbLane X y := .of_noUb (Sched.safe_noUb (hs.2 X hX)) y
  have hlen : 0 < (X.tr y).length := by
    by_contra h0
    exact hr (Sched.released_nil (List.length_eq_zero_iff.mp (by omega)))
  obtain ⟨e, he⟩ : ∃ e, X.get (y, (X.tr y).length - 1) = some e :=
    ⟨_, List.getElem?_eq_getElem (show (X.tr y).length - 1 < (X.tr y).length by omega)⟩
  have hblk : ¬ Sched.Unblocking e.kind := fun hu => hr (Sched.released_of_unblocking he hu)
  have hbpc := Lib.blocked_pc hX he (nu.kind he) hblk
  refine (Prog.block_any hp hX hf he (nu.kind he) (nu.before _) hbpc).2.1 ?_
  unfold Lib.StateGone
  rw [Nat.sub_add_cancel hlen]
  exact hgone


/-- **A mate of a released lane is released, or an extension is counted.** -/
public theorem Prog.warp_rel (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hm : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) {P : Nat → Prop} :
    WarpRel Q L m X P := by
  intro x y σ σ' hx hy hsw hσ hcx hσ' hcy hn hpre hrel
  by_contra hno
  have hr : ¬ Step.Released L X y := fun h => hno (.inl h)
  have hX := hm.1
  have hsafe := hs.2 X hX
  have hu0 : ¬ HasUb X := Sched.safe_noUb hsafe
  have safe : ¬ Race L X := fun h => hsafe (by simp [Unsafe, h])
  have nu : ∀ z, NoUbLane X z := fun z => .of_noUb hu0 z
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have hyt : y < L.threads := hsw.1.2.1
  have hxt : x < L.threads := hsw.1.1
  have hlen : 0 < (X.tr y).length := by
    by_contra h0
    exact hr (Sched.released_nil (List.length_eq_zero_iff.mp (by omega)))
  have hk1 : (X.tr y).length - 1 + 1 = (X.tr y).length := Nat.sub_add_cancel hlen
  obtain ⟨e, he⟩ : ∃ e, X.get (y, (X.tr y).length - 1) = some e :=
    ⟨_, List.getElem?_eq_getElem (show (X.tr y).length - 1 < (X.tr y).length by omega)⟩
  have hblk : ¬ Sched.Unblocking e.kind := fun hu => hr (Sched.released_of_unblocking he hu)
  have hue := (nu y).kind he
  have hbpc := Lib.blocked_pc hX he hue hblk
  obtain ⟨⟨σ0, hσ0, hnc⟩, -, hpair⟩ := Prog.block_any hp hX hf he hue ((nu y).before _) hbpc
  have hpp := hpair _ ⟨σ', by rw [hk1]; exact hσ', hcy, rfl⟩
  have hlt := hpre _ hk1 hσ0 hnc
  have clash : Sched.threadTime (schedule Q L) X x ≤
      Sched.timeAt (schedule Q L) X y ((X.tr y).length - 1) → False := fun h => by
    rw [Sched.threadTime_of hσ] at h
    simp only [Sched.timeAt, hσ0] at h
    omega
  have rel_of_ready : Ready L X (y, (X.tr y).length - 1) → False := fun rdy =>
    hr ⟨fun _ _ hget _ => by rw [he] at hget; cases hget; exact rdy⟩
  have tcInfo : (∃ id cnt md, e.kind = .bar id cnt md) ∨
      ∃ pc tk, e = ⟨pc, .tc tk⟩ ∧ isTcColl e = true := by
    rcases Lib.pairs_kind hX he hue hblk hpp with b | ⟨grp, dst, act, hk⟩ | hd
    · exact .inl b
    · obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      exact .inr ⟨pc, _, rfl, by simp [isTcColl]⟩
    · obtain ⟨pc, kd⟩ := e
      cases kd <;> simp [isTcData] at hd
      case tc tk => exact .inr ⟨pc, tk, rfl, by cases tk <;> simp_all [isTcColl]⟩
  rcases tcInfo with ⟨id, cnt, md, hkind⟩ | ⟨pc, tk, rfl, htc⟩
  · -- a barrier
    obtain ⟨pc, kd⟩ := e
    simp only at hkind
    subst hkind
    obtain ⟨rfl, hcls⟩ := Lib.recorded_bar hX hp.block he
    by_cases hle : (X.tr x).countP (Execution.isBarId id) ≤
        ((X.tr y).take ((X.tr y).length - 1)).countP (Execution.isBarId id)
    · refine absurd ?_ clash
      rcases hcls with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, hfull⟩ | ⟨rfl, hcnt, hhalf⟩
      · exact (Export.bar1_lag hp hX hf words hxt (nu x) he hle).2
      · have full : ∀ q ∈ Lib.pairs, q.1 ∈ BarRow.fullZeroSites → q.1 = 14 ∧ q.2 = 17 := by
          decide +kernel
        obtain ⟨rfl, h17⟩ := full _ hpp hfull
        have two := Startup.Export.bars_shfl hp hX (nu y) ⟨σ', hσ', h17⟩
        have step := countP_take_succ (p := Execution.isBarId 0) he (by simp [Execution.isBarId])
        rw [hk1, List.take_length] at step
        exact (Export.bar0_early_lag hp hX hf he
          (show ((X.tr y).take ((X.tr y).length - 1)).countP (Execution.isBarId 0) < 2 by omega)
          hxt (nu x) hle).2
      · have hc' : cnt = some 128 := by simpa [BarRow.recCnt, hp.block] using hcnt
        subst hc'
        rcases Export.barZeroSources hp hX (y, (X.tr y).length - 1) pc (some 128) ⟨.sync, he⟩
          hyt with h | ⟨-, hgp, -⟩
        · cases h
        · have h4 : y % L.block / 32 < 4 := Finset.mem_range.mp hgp
          have lg : y % L.block < 128 := by omega
          have hw := hsw.2
          have lx : x % L.block < 128 := by omega
          exact (Protocol.Bar.loop_lag hp hX hf safe nu hxt hsw.1.2.2 lg lx he hle).2
    · exact hr (Prog.mate_bar hX hp.block hsw he (by omega) hrel)
  · -- a warp-collective `tcgen05` event
    have hk : X.TcK (y, (X.tr y).length - 1)
        (((X.tr y).take ((X.tr y).length - 1)).countP isTcColl) := ⟨⟨_, he, htc⟩, rfl⟩
    by_cases hle : (X.tr x).countP isTcColl ≤ ((X.tr y).take ((X.tr y).length - 1)).countP isTcColl
    · exact absurd (Prog.tc_lag hp hX hf safe hu0 hyt hxt (sameWarp_symm hsw) hk hle) clash
    obtain ⟨j, ex, hj, hq, ho⟩ := NamedBar.exists_ordinal isTcColl (X.tr x)
      (show ((X.tr y).take ((X.tr y).length - 1)).countP isTcColl < (X.tr x).countP isTcColl
        by omega)
    obtain ⟨px, tkx, rfl⟩ := isTcColl_tc hq
    have hxj : X.get (x, j) = some ⟨px, .tc tkx⟩ := hj
    have hkx : X.TcK (x, j) _ := ⟨⟨_, hxj, hq⟩, ho⟩
    have rdy := Prog.ready_of_count hX hxj
      (by cases tkx <;> simp_all [isTcColl, Kind.resume, TcKind.resume]) hrel
    have hall := Prog.tc_all hsw hxj hq hkx rdy
    have data : (∀ grp dst act, tk ≠ .resource grp dst act) → False := fun ht =>
      rel_of_ready (Sched.tc_ready_of_done (e := (y, (X.tr y).length - 1)) hyt he ht hk hall)
    cases tk with
    | resource grp dst act =>
      have hto := Export.tmem_ops hp hX hf
      have shape := (hto.event hyt he).2.2
      have hres : pc ∈ Lib.resPcs := Export.tmem_event_pc hX he (by simp [Tmem.Pair.isTmemOp])
      have p15 : pc = 15 := by
        have : ∀ q ∈ Lib.pairs, q.1 ∈ Lib.resPcs → q.1 = 15 := by decide
        exact this _ hpp hres
      have ops := (Export.tc_tmem hp hX hf he htc).2.2.1 p15
      have hna : ∀ n, act ≠ .alloc n := fun n h => by
        rw [ops] at shape
        subst h
        simp [Tmem.Pair.TmemShape] at shape
      rcases Prog.tmem_rel_or_ext hp hs hX hf hyt he hna hall with h | h
      · exact hr h
      · exact hno (.inr h)
    | _ => exact data (by simp)

end PTX.Kernels.InklingRelDecode.Proof.Top
