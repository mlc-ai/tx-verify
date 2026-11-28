-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.TcVec
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Kernels.InklingRelDecode.Proof.Lib.ResPcs
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Kernels.InklingRelDecode.Proof.Common.TcCount
import Kernels.InklingRelDecode.Proof.Common.ResourceCount
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.ResourceSites
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.Table

@[expose] public section

/-! # The `tcgen05` data events before a collective event, in closed form

Every collective `tcgen05` event is a data lane's (a thread of the first four warps). The numbers
of earlier events at the positions of `Lib.dataPcs` before such an event at `pc` are `Lib.tcVec`
of the round `i` and the visits `R` of the optional rendezvous. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Tmem.Pair

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat}

private theorem no_ub {pc : Nat} {k : Kind} (tc : isTcColl ⟨pc,k⟩ = true) :
    ∀ f, (⟨pc,k⟩ : Event).kind ≠ .ub f := by
  intro f h
  change k = .ub f at h
  subst h
  simp [isTcColl] at tc

private theorem soft_vec (s : Softmax.Site) (i R : Nat) (h : s.pc ∈ Lib.loopTcPcs) :
    Lib.dataPcs.map (Softmax.softCount s i R) = Lib.tcVec s.pc i R 0 := by
  simp only [Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at h
  cases s <;> first
    | (simp only [Softmax.Site.pc] at h; omega)
    | (exfalso; revert h; decide)
    | (simp (config := {decide := true}) [Lib.dataPcs,Softmax.softCount,Lib.tcVec,
        Softmax.afterLdS,Softmax.afterWaitLd,Softmax.afterTmemSt,
        Softmax.afterTmemWait])

private theorem epi_vec (skip : Bool) (s : Epilogue.Site) (l R : Nat)
    (live : s = .waitLd → skip = false) (h : s.pc = 2607 ∨ s.pc = 2608 ∨ s.pc = 2851) :
    Lib.dataPcs.map (fun P => Softmax.softCount .epilogue l R P + Epilogue.epiCount skip s P) =
      Lib.tcVec s.pc l R (if skip then 0 else 1) := by
  cases s <;> first
    | (exfalso; simp only [Epilogue.Site.pc,Epilogue.storePc] at h; omega)
    | (simp (config := {decide := true}) [Lib.dataPcs,Softmax.softCount,Lib.tcVec,
        Epilogue.epiCount,Epilogue.afterLoad,Epilogue.afterWaitLd,
        Softmax.afterLdS,Softmax.afterWaitLd,Softmax.afterTmemSt,Softmax.afterTmemWait]
       try (cases skip <;> simp_all))

/-- The state before a collective `tcgen05` event and the event's position. -/
private theorem tc_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc k} (he : X.get (g,j) = some ⟨pc,k⟩) (tc : isTcColl ⟨pc,k⟩ = true) :
    ∃ s, stateAt (thread Q L) X g j = some (some s) ∧ pc = (thread Q L g).pc s ∧
      (thread Q L g).inv s ∧ TcInv s ∧ j ≤ (X.tr g).length ∧
      (isTmemOp ⟨pc,k⟩ = true ∨ pc ∈ Lib.dataPcs) := by
  have nu := no_ub tc
  have hg := lt_of_get hX he
  obtain ⟨s,hs,_⟩ := good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ f h => nu f (congrArg Event.kind h)) (hf g hg j)
  have nub := noUbBefore_of_get hX he
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  refine ⟨s,hs,event_pcU (fun g hg => thread_sound hp hg) hX he hs nu,
    (reached_table hf hg nub hs).1,tc_inv hp hX hf hg hk hs nub,hk,?_⟩
  have res := Lib.tcColl_event hX he nu
  rw [tc] at res
  have := res.symm
  simpa only [Bool.or_eq_true,decide_eq_true_eq] using this

private theorem startup_tc_pc (site : Startup.Site) : site.pc ∉ Lib.tcVecPcs := by
  simp only [Lib.tcVecPcs,Lib.dataPcs]
  cases site <;> first | decide | (rename_i r; cases r <;> decide)

/-- A paired Tensor Memory event is at one of the paired instructions' positions. -/
public theorem tmem_event_pc (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {e : Event}
    (he : X.get i = some e) (res : isTmemOp e = true) : e.pc ∈ Lib.resPcs :=
  tmem_op_pc hX he res

/-- **A collective `tcgen05` event is a data lane's.** -/
public theorem tc_data_lane (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc k} (he : X.get (g,j) = some ⟨pc,k⟩) (tc : isTcColl ⟨pc,k⟩ = true) :
    g%L.block < 128 := by
  obtain ⟨s,hs,hpc,hi,-,hk,ty⟩ := tc_state hp hX hf he tc
  rcases ty with res|dpc
  · obtain ⟨_,grp,dst,act,eq⟩ := tmemOp_resource res
    simp only [Event.mk.injEq] at eq
    obtain ⟨-,rfl⟩ := eq
    obtain ⟨_,ops⟩ := tmem_ops hp hX hf
    have := (ops (lt_of_get hX he) he).1
    omega
  · by_cases c : 574<pc ∧ pc<2331
    · have pl := state_role s
      rw [hpc] at c
      obtain ⟨w,e,d,n,rfl⟩ := pl.softmax c.1 c.2
      exact data_warp hp hX hk hs
    · have pl := state_role s
      simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at dpc
      obtain ⟨w,e,d,n,rfl⟩ := pl.epilogue (by omega) (by omega) hi
      exact data_warp hp hX hk hs

private theorem startup_site_ne (site : Startup.Site) : site.pc ≠ 2851 ∧ site.pc ≠ 2854 := by
  cases site <;> first
    | (constructor <;> decide)
    | (rename_i r; cases r <;> (constructor <;> decide))

/-- Where a collective `tcgen05` event is: a startup state, a Softmax state at one of the loop's
eight positions, or an epilogue state at the load, its wait or the deallocation. -/
private theorem tc_where (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc k} (he : X.get (g,j) = some ⟨pc,k⟩) (tc : isTcColl ⟨pc,k⟩ = true) :
    ∃ s : (thread Q L g).D, stateAt (thread Q L) X g j = some (some s) ∧ TcInv s ∧
      (thread Q L g).inv s ∧ j ≤ (X.tr g).length ∧ NoUbBefore X g j ∧
      ((∃ st n, s = (.inl st,n) ∧ pc = st.site.pc ∧ (pc = 11 ∨ pc = 15)) ∨
       (∃ w ent d n, s = softState w ent d n ∧ pc = d.site.pc ∧ pc ∈ Lib.loopTcPcs) ∨
       (∃ w ent d n, s = epiState w ent d n ∧ pc = d.site.pc ∧
         (pc = 2607 ∨ pc = 2608 ∨ pc = 2851))) := by
  obtain ⟨⟨s,n⟩,hs,hpc,hi,inv,hk,ty⟩ := tc_state hp hX hf he tc
  have hu := no_ub tc
  refine ⟨_,hs,inv,hi,hk,noUbBefore_of_get hX he,?_⟩
  rcases s with st|⟨r,d⟩
  · refine .inl ⟨st,n,rfl,hpc,?_⟩
    change pc = st.site.pc at hpc
    rcases ty with res|dpc
    · have := tmem_op_pc hX he res
      change pc ∈ Lib.resPcs at this
      simp only [Lib.resPcs,List.mem_cons,List.not_mem_nil,or_false] at this
      have bound := startup_site_ne st.site
      omega
    · exact (startup_data_pc st.site (List.mem_cons_of_mem _ dpc) hpc.symm).elim
  rcases r with r|r
  swap
  · exfalso
    change pc = Startup.Entry.pc r at hpc
    rcases ty with res|dpc
    · have := tmem_op_pc hX he res
      change pc ∈ Lib.resPcs at this
      simp only [Lib.resPcs,List.mem_cons,List.not_mem_nil,or_false] at this
      cases r <;> simp only [Startup.Entry.pc] at hpc <;> omega
    · simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at dpc
      cases r <;> simp only [Startup.Entry.pc] at hpc <;> omega
  cases r with
  | dispatch w x =>
    exfalso
    rcases ty with res|dpc
    · have := worker_no_resource hp hX hf he hu hs
      rw [res] at this
      cases this
    · exact worker_data_pc hi (List.mem_cons_of_mem _ dpc) hpc.symm
  | prologue w =>
    have rsc := data_resource hp hX he hu hs
    rcases d with d|⟨ent,d|⟨_,d⟩⟩
    · exfalso
      change pc = d.site.pc at hpc
      have range := d.site.pc_range
      rcases ty with res|dpc
      · rw [res] at rsc
        have := of_decide_eq_true rsc.symm
        change d.site.pc = 2851 at this
        omega
      · simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at dpc
        omega
    · change pc = d.site.pc at hpc
      have range := d.site.pc_range
      refine .inr (.inl ⟨w,ent,d,n,rfl,hpc,?_⟩)
      rcases ty with res|dpc
      · rw [res] at rsc
        have := of_decide_eq_true rsc.symm
        change d.site.pc = 2851 at this
        exfalso
        rcases range with r|r
        · omega
        · rw [r] at this; change 2565 = 2851 at this; omega
      · simp only [Lib.dataPcs,Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at dpc ⊢
        rcases range with r|r
        · omega
        · rw [r] at hpc; change pc = 2565 at hpc; omega
    · change pc = d.site.pc at hpc
      have range := d.site.pc_range
      refine .inr (.inr ⟨w,ent,d,n,rfl,hpc,?_⟩)
      rcases ty with res|dpc
      · rw [res] at rsc
        have := of_decide_eq_true rsc.symm
        change d.site.pc = 2851 at this
        omega
      · simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at dpc
        omega

/-- **A collective `tcgen05` event is at one of the data lane's positions** (the startup's two
resource instructions, the Softmax loop's eight, the epilogue's load, wait and deallocation). -/
public theorem tc_pc_where (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc k} (he : X.get (g,j) = some ⟨pc,k⟩) (tc : isTcColl ⟨pc,k⟩ = true) :
    pc = 11 ∨ pc = 15 ∨ pc ∈ Lib.loopTcPcs ∨ pc = 2607 ∨ pc = 2608 ∨ pc = 2851 := by
  obtain ⟨s,hs,inv,hi,hk,nub,wh⟩ := tc_where hp hX hf he tc
  rcases wh with ⟨st,n',eq,hpc,res⟩|⟨w,ent,d,n',eq,hpc,loop⟩|⟨w,ent,d,n',eq,hpc,where_⟩
  · exact res.elim .inl (fun h => .inr (.inl h))
  · exact .inr (.inr (.inl loop))
  · rcases where_ with h|h|h
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact .inr (.inr (.inr (.inr (.inr h))))

private theorem epi_site_pc (s : Epilogue.Site) (h : s.pc = 2607 ∨ s.pc = 2608 ∨ s.pc = 2851) :
    (s.pc = 2607 → s = .load) ∧ (s.pc = 2608 → s = .waitLd) ∧ (s.pc = 2851 → s = .dealloc) := by
  cases s <;> first
    | (simp only [Epilogue.Site.pc,Epilogue.storePc] at h ⊢; omega)
    | (refine ⟨?_,?_,?_⟩ <;> intro h2 <;> first | rfl | (exfalso; revert h2; decide))

private theorem soft_site_pc (s : Softmax.Site) (h : s.pc ∈ Lib.loopTcPcs) :
    (s.pc = 2260 ∨ s.pc = 2261 ∨ s.pc = 2328 ∨ s.pc = 2329 → Softmax.needsPrevious s = true) ∧
    (s.pc = 2328 ∨ s.pc = 2329 → Softmax.visited s = true) ∧
    (s ≠ .epilogue ∧ s ≠ .setMaxReg ∧ s ≠ .bar0 ∧ ∀ j, s ≠ .pre j) ∧
    (s.pc = 2260 → s = .ldO) ∧ (s.pc = 1009 → s = .tmemSt) := by
  simp only [Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at h
  cases s <;> first
    | (simp only [Softmax.Site.pc] at h; omega)
    | (exfalso; revert h; decide)
    | (refine ⟨?_,?_,⟨?_,?_,?_,?_⟩,?_,?_⟩ <;>
        simp [Softmax.needsPrevious,Softmax.visited,Softmax.Site.pc])

/-- **The earlier data events before a collective `tcgen05` event** are counted by the position of
the event, the round `i` (the launch's loop count in the epilogue) and the visits `R` of the
optional rendezvous, which are the earlier events at pc 2326; `e'` is the number of the
epilogue's loads at the deallocation, which the launch's loop count fixes. -/
public theorem tc_counts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc k} (he : X.get (g,j) = some ⟨pc,k⟩) (tc : isTcColl ⟨pc,k⟩ = true) :
    ∃ i R e', Lib.dataPcs.map (fun P => ((X.tr g).take j).countP (fun x => x.pc == P)) =
      Lib.tcVec pc i R e' ∧ ((X.tr g).take j).countP (fun x => x.pc == 2326) = R ∧
      (pc = 11 ∨ pc = 15 ∨ pc ∈ Lib.tcVecPcs) ∧
      (pc ∈ Lib.loopTcPcs → i < Lib.blocksOf Q L (g/L.block)) ∧
      ((pc = 2260 ∨ pc = 2261 ∨ pc = 2328 ∨ pc = 2329) → 1 ≤ i) ∧
      ((pc = 2328 ∨ pc = 2329) → 1 ≤ R) ∧
      ((pc = 2607 ∨ pc = 2608 ∨ pc = 2851) → i = Lib.blocksOf Q L (g/L.block)) ∧
      ((pc = 2607 ∨ pc = 2608) → Lib.blocksOf Q L (g/L.block) ≠ 0) ∧
      (pc = 2851 → e' = if Lib.blocksOf Q L (g/L.block) = 0 then 0 else 1) ∧
      ((pc = 2260 ∨ pc = 1009) → ((X.tr g).take j).countP (Execution.isBarId 0) + 2 =
        3 + 5 * Iface.preloadCount Q L (g/L.block) + 4 * i + (if pc = 2260 then 2 else 3) + R) := by
  obtain ⟨⟨s,n⟩,hs,inv,hi,hk,nub,wh⟩ := tc_where hp hX hf he tc
  have hg := lt_of_get hX he
  have cnt (P : Nat) : ((X.tr g).take j).countP (fun x => x.pc == P) = n (.atPc P) :=
    (fcount hs (.atPc P)).symm
  rcases wh with ⟨st,n',eq,hpc,res⟩|⟨w,ent,d,n',eq,hpc,loop⟩|⟨w,ent,d,n',eq,hpc,where_⟩
  · cases eq
    change Zero n at inv
    refine ⟨0,0,0,?_,(cnt 2326).trans (inv 2326 (by simp [watchPcs])),by omega,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [Lib.tcVec_off (hpc ▸ startup_tc_pc st.site)]
      rw [List.map_congr_left (g := fun _ => 0) (fun P hP => by
        rw [cnt P]; exact inv P (List.mem_cons_of_mem _ hP))]
      simp [Lib.dataPcs]
    all_goals intro h
    all_goals first
      | omega
      | (simp only [Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at h; omega)
  · cases eq
    obtain ⟨cntInv,vis⟩ := inv
    have lim := reached_loop hp hX hg hk hs
    have prev := shfl_previous hp hX hk hs nub
    obtain ⟨sp,sv,⟨s1,s2,s3,s4⟩,sl,st⟩ := soft_site_pc d.site (hpc ▸ loop)
    have loop' := loop
    simp only [Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at loop'
    refine ⟨d.i,n (.atPc 2326),0,?_,cnt 2326,.inr (.inr ?_),fun _ => ?_,fun h => ?_,fun h => ?_,
      fun h => ?_,fun h => ?_,fun h => ?_,fun h => ?_⟩
    · rw [List.map_congr_left (g := Softmax.softCount d.site d.i (n (.atPc 2326)))
        (fun P hP => by rw [cnt P]; exact cntInv P hP),hpc]
      exact soft_vec d.site _ _ (hpc ▸ loop)
    · refine List.mem_append_left _ ?_
      simp only [Lib.loopTcPcs,Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at loop ⊢
      omega
    · rw [← lim.1]
      exact hi.1.loop s1 s2 s3 s4
    · exact prev (sp (hpc ▸ h))
    · exact vis (sv (hpc ▸ h))
    · omega
    · omega
    · omega
    · have ord := data_ordinal hp hX hk hs nub
      have c0 : n (.bar 0) = ((X.tr g).take j).countP (Execution.isBarId 0) := by
        have := fcount hs (.bar 0)
        rw [cls_bar0] at this
        exact this
      rcases h with h|h
      · simp only [sl (hpc ▸ h),Softmax.fixedCount,Softmax.syncPosition] at ord
        simp only [h,↓reduceIte]
        omega
      · simp only [st (hpc ▸ h),Softmax.fixedCount,Softmax.syncPosition] at ord
        simp only [h,show (1009:Nat)≠2260 by decide,↓reduceIte]
        omega
  · cases eq
    obtain ⟨cntInv,live⟩ := inv
    have lim := reached_loop hp hX hg hk hs
    have w := where_
    refine ⟨ent.limit,n (.atPc 2326),if (epiEntry ent (g%L.block)).skip then 0 else 1,?_,cnt 2326,
      .inr (.inr ?_),fun h => ?_,fun h => ?_,fun h => ?_,fun _ => lim.1,fun h => ?_,fun h => ?_,
      fun h => ?_⟩
    · rw [List.map_congr_left (g := fun P => Softmax.softCount .epilogue ent.limit
        (n (.atPc 2326)) P+Epilogue.epiCount (epiEntry ent (g%L.block)).skip d.site P)
        (fun P hP => by rw [cnt P]; exact cntInv P hP),hpc]
      exact epi_vec _ d.site _ _ (fun h => live (.inr (.inr h))) (hpc ▸ where_)
    · simp only [Lib.tcVecPcs,Lib.dataPcs,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false]
      omega
    all_goals try first
      | (simp only [Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at h; omega)
      | omega
    · have site := epi_site_pc d.site (hpc ▸ (by omega : pc = 2607 ∨ pc = 2608 ∨ pc = 2851))
      have off : (epiEntry ent (g%L.block)).skip = false := by
        rcases h with h|h
        · exact live (.inr (.inl (site.1 (hpc ▸ h))))
        · exact live (.inr (.inr (site.2.1 (hpc ▸ h))))
      have z : decide (ent.limit = 0) = false := lim.2.symm.trans off
      rw [← lim.1]
      simpa using z
    · have sk : (epiEntry ent (g%L.block)).skip = decide (ent.limit = 0) := lim.2
      rw [sk,← lim.1]
      by_cases z : ent.limit = 0 <;> simp [z]

private theorem tmem_off (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : g<L.threads) (w0 : g%L.block/32 ≠ 0) :
    tmemOps ((X.tr g).take j) = 0 := by
  obtain ⟨_,ops⟩ := tmem_ops hp hX hf
  apply List.countP_eq_zero.mpr
  intro ev mem
  obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take mem)
  intro r
  obtain ⟨_,grp,dst,act,rfl⟩ := tmemOp_resource r
  exact w0 (ops hg (show X.get (g,n) = _ from hn)).1

/-- **The paired Tensor Memory operations before a collective `tcgen05` event**: the allocation and
the relinquishment are warp zero's first two events, and warp zero has made both before every
other collective event. -/
public theorem tc_tmem (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc k} (he : X.get (g,j) = some ⟨pc,k⟩) (tc : isTcColl ⟨pc,k⟩ = true) :
    ((pc = 11 ∨ pc = 15 ∨ pc = 2851) → g%L.block/32 = 0) ∧
    (pc = 11 → tmemOps ((X.tr g).take j) = 0) ∧ (pc = 15 → tmemOps ((X.tr g).take j) = 1) ∧
    (pc ≠ 11 → pc ≠ 15 → tmemOps ((X.tr g).take j) = if g%L.block/32 = 0 then 2 else 0) := by
  obtain ⟨s,hs,-,-,hk,nub,wh⟩ := tc_where hp hX hf he tc
  have hg := lt_of_get hX he
  have hu := no_ub tc
  obtain ⟨_,ops⟩ := tmem_ops hp hX hf
  have win : (pc = 11 ∨ pc = 15 ∨ pc = 2851) → g%L.block/32 = 0 := by
    intro h
    obtain ⟨-,-,-,-,-,-,ty⟩ := tc_state hp hX hf he tc
    rcases ty with res|dpc
    · obtain ⟨_,grp,dst,act,eq⟩ := tmemOp_resource res
      simp only [Event.mk.injEq] at eq
      obtain ⟨-,rfl⟩ := eq
      exact (ops hg he).1
    · simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at dpc
      omega
  by_cases w0 : g%L.block/32 = 0
  swap
  · have z : tmemOps ((X.tr g).take j) = 0 := tmem_off hp hX hf hg w0
    exact ⟨win,fun h => (w0 (win (.inl h))).elim,fun h => (w0 (win (.inr (.inl h)))).elim,
      fun _ _ => by simp [w0,z]⟩
  have low : g%L.block<32 := by omega
  rw [resource_prefix hp hX hf hg low hk nub hs]
  rcases wh with ⟨st,n,rfl,hpc,res⟩|⟨w,ent,d,n,rfl,hpc,loop⟩|⟨w,ent,d,n,rfl,hpc,wh2⟩
  · have ev := start_ev hp hX he hs hu
    obtain ⟨site,t,x,w'⟩ := st
    refine ⟨win,?_,?_,?_⟩
    all_goals intro h1
    all_goals try intro h2
    all_goals cases site
    all_goals first
      | (obtain ⟨col,-,eq⟩ := ev
         simp only [Event.mk.injEq] at eq
         obtain ⟨-,rfl⟩ := eq
         simp [isTcColl] at tc)
      | (exfalso; simp [Startup.Site.pc] at hpc; rename_i r; cases r <;>
          simp [Startup.Entry.pc] at hpc <;> omega)
      | simp_all [Startup.Ev,Startup.resourceCount,Startup.Site.pc,resourcePhase,
          Nat.not_le_of_lt low]
  · simp only [Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at loop
    refine ⟨win,fun h1 => ?_,fun h1 => ?_,fun _ _ => ?_⟩
    · omega
    · omega
    · simp [w0,resourcePhase,dataEnd,softEnd]
  · refine ⟨win,fun h1 => ?_,fun h1 => ?_,fun _ _ => ?_⟩
    · omega
    · omega
    · have : ¬ d.site.pc = 2855 := by omega
      simp [w0,resourcePhase,dataEnd,softEnd,this]

private theorem exit_vec (skip : Bool) (l R : Nat) :
    Lib.dataPcs.map (fun P => Softmax.softCount .epilogue l R P +
      Epilogue.epiCount skip .exit P) = Lib.tcVec 2851 l R (if skip then 0 else 1) := by
  cases skip <;> simp (config := {decide := true}) [Lib.dataPcs,Softmax.softCount,Lib.tcVec,
    Epilogue.epiCount,Epilogue.afterLoad,Epilogue.afterWaitLd,Softmax.afterLdS,
    Softmax.afterWaitLd,Softmax.afterTmemSt,Softmax.afterTmemWait]

/-- **A data lane's exit has made every data event of the loop and the epilogue**, and warp zero
has made its three paired Tensor Memory operations. -/
public theorem exit_counts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc} (he : X.get (g,j) = some ⟨pc,.exit⟩) (lg : g%L.block < 128) :
    ∃ R e', Lib.dataPcs.map (fun P => ((X.tr g).take j).countP (fun x => x.pc == P)) =
      Lib.tcVec 2851 (Lib.blocksOf Q L (g/L.block)) R e' ∧
      e' = (if Lib.blocksOf Q L (g/L.block) = 0 then 0 else 1) ∧
      tmemOps ((X.tr g).take j) = if g%L.block/32 = 0 then 3 else 0 := by
  have hg := lt_of_get hX he
  obtain ⟨s,hs,_⟩ := good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ _ h => by cases h) (hf g hg j)
  have nub := noUbBefore_of_get hX he
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have inv := tc_inv hp hX hf hg hk hs nub
  have hpc := event_pcU (fun g h => thread_sound hp h) hX he hs (by simp)
  obtain ⟨_,_,_,_,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX he hs (by simp)
  have ret' := Lib.ret_pc' hc fire rfl
  simp only [Lib.retPcs,List.mem_singleton] at ret'
  have ret : pc = 2855 := hpc.trans ret'
  have cnt (P : Nat) : ((X.tr g).take j).countP (fun x => x.pc == P) = s.2 (.atPc P) :=
    (fcount hs (.atPc P)).symm
  obtain ⟨d,n⟩ := s
  rcases d with d|⟨r,d⟩
  · exfalso
    change pc = d.site.pc at hpc
    have h2 : d.site.pc ≠ 2855 := by
      generalize d.site=site
      cases site <;> first | decide | (rename_i r; cases r <;> decide)
    omega
  rcases r with r|r
  swap
  · exfalso
    change pc = Startup.Entry.pc r at hpc
    cases r <;> simp only [Startup.Entry.pc] at hpc <;> omega
  cases r with
  | dispatch w x =>
    exact absurd (worker_warp hp hX hk hs).1 (Nat.not_le.mpr lg)
  | prologue w =>
    rcases d with d|⟨ent,d|⟨_,d⟩⟩
    · exfalso
      change pc = d.site.pc at hpc
      have := d.site.pc_range
      omega
    · exfalso
      change pc = d.site.pc at hpc
      rcases d.site.pc_range with r|r
      · omega
      · rw [r] at hpc; change pc = 2565 at hpc; omega
    · change pc = d.site.pc at hpc
      have site : d.site = .exit := by
        have h : d.site.pc = 2855 := by omega
        generalize d.site = s at h ⊢
        cases s <;> first
          | rfl
          | (exfalso; simp only [Epilogue.Site.pc,Epilogue.storePc] at h; omega)
      obtain ⟨cntInv,-⟩ := inv
      have lim := reached_loop hp hX hg hk hs
      refine ⟨n (.atPc 2326),if (epiEntry ent (g%L.block)).skip then 0 else 1,?_,?_,?_⟩
      · rw [List.map_congr_left (g := fun P => Softmax.softCount .epilogue ent.limit
          (n (.atPc 2326)) P+Epilogue.epiCount (epiEntry ent (g%L.block)).skip .exit P)
          (fun P hP => by rw [cnt P]; simpa [site] using cntInv P hP),exit_vec,lim.1]
      · have sk : (epiEntry ent (g%L.block)).skip = decide (ent.limit = 0) := lim.2
        rw [sk,lim.1]
        by_cases z : Lib.blocksOf Q L (g/L.block) = 0 <;> simp [z]
      · by_cases w0 : g%L.block/32 = 0
        · simp only [w0,↓reduceIte]
          exact exit_ops hp hX hf hg w0 he
        · simp only [w0,↓reduceIte]
          exact tmem_off hp hX hf hg w0

end PTX.Kernels.InklingRelDecode.Proof.Export
