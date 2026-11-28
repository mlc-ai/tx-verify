-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Lib.RegLedger
import Kernels.InklingRelDecode.Proof.Common.RequestLedger
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.WorkerIdle
import Lemmas.CtaBarrier.CtaBarrierRoundHistory
public import Kernels.InklingRelDecode.Proof.Lib.RegSchedule
import Lemmas.Flow.UbStop
import Lemmas.Flow.NotBulk
import Kernels.InklingRelDecode.Proof.Lib.ResPcs

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **The ledger of an event**: the position, the barrier-1 events and the register requests
before it satisfy `ledgerOk`. -/
theorem ledger_event {e} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (he : X.get (g,k)=some e) (hu : ∀ f, e.kind≠.ub f) :
    Lib.ledgerOk e.pc (((X.tr g).take k).countP (Execution.isBarId 1))
      (((X.tr g).take k).countP SetMaxNReg.isRequest) = true := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => hu f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have nu := Frame.noUbBefore_of_get hX he
  have len := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨count,ok⟩ := request_prefix hp hX words len nu hs
  rw [Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu,
    publication_prefix hp hX hg nu hs,count]
  exact state_ledger s ok

/-- The state before an event without undefined behaviour: clean, with its table invariant, at
the event's position, its request count that of the prefix. -/
private theorem event_state {e : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some e) (hu : ∀ f, e.kind≠.ub f) :
    ∃ s, Frame.stateAt (thread Q L) X g k=some (some s) ∧ tableInv Q L g s ∧ requestClean s ∧
      (thread Q L g).pc s=e.pc ∧ requests s=((X.tr g).take k).countP SetMaxNReg.isRequest := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => hu f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have nu := Frame.noUbBefore_of_get hX he
  have len := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨count,ok⟩ := request_prefix hp hX words len nu hs
  have pcs := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  exact ⟨s,hs,reached_table hf hg nu hs,ok,pcs.symm,count.symm⟩

private theorem request_mem {pc inc n inst} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) : pc ∈ Lib.requestPcs := by
  obtain ⟨_,bad⟩ | ⟨t,ins,o,_,code,fire⟩ := get_source hX he
  · cases bad
  have h := (Lib.request_fires code fire).1
  exact of_decide_eq_true (h.symm.trans rfl)

/-- The state before a request, with its role and position. -/
private theorem request_state {pc inc n inst} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) :
    ∃ s, Frame.stateAt (thread Q L) X g k=some (some s) ∧ tableInv Q L g s ∧
      (thread Q L g).pc s=pc ∧ requests s=((X.tr g).take k).countP SetMaxNReg.isRequest ∧
      ((DataRole s ∧ Lib.dataReq pc = true) ∨ (WorkerRole s ∧ Lib.workerReq pc = true)) := by
  obtain ⟨s,hs,tab,ok,pcs,count⟩ := event_state hp hX hf words he (fun _ => nofun)
  have hit : (thread Q L g).pc s ∈ Lib.requestPcs := pcs ▸ request_mem hX he
  have act : ∀ st nn, s = (.inl st,nn) → Startup.enterOf st = none := by
    rintro st nn rfl
    exact Code.gatedExit_none.mp tab.1.2
  refine ⟨s,hs,tab,pcs,count,?_⟩
  have grp := state_group s ok act hit
  rw [pcs] at grp
  exact grp

/-- **A request is made by the default partition at its positions, or by a worker at its.** -/
theorem request_group {pc inc n inst} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) :
    (g%L.block<128 ∧ Lib.dataReq pc = true) ∨ (128≤g%L.block ∧ Lib.workerReq pc = true) := by
  have len := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨s,hs,_,_,_,grp⟩ := request_state hp hX hf words he
  obtain ⟨s0,n0⟩ := s
  rcases s0 with s0 | ⟨r,s0⟩
  · rcases grp with ⟨h,_⟩ | ⟨h,_⟩ <;> exact h.elim
  · rcases r with r | r
    · cases r with
      | prologue w =>
        rcases grp with ⟨_,dq⟩ | ⟨h,_⟩
        · exact .inl ⟨data_warp hp hX len hs,dq⟩
        · exact h.elim
      | dispatch w x =>
        rcases grp with ⟨h,_⟩ | ⟨_,wq⟩
        · exact h.elim
        · exact .inr ⟨(worker_warp hp hX len hs).1,wq⟩
    · rcases grp with ⟨h,_⟩ | ⟨h,_⟩ <;> exact h.elim

private theorem loader_pcs (s : Loader.Site) (h : s.pc ∈ Lib.requestPcs) :
    s.pc=2344 ∨ s.pc=2420 ∨ s.pc=2337 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_pcs (s : Mma.Site) (h : s.pc ∈ Lib.requestPcs) :
    s.pc=2422 ∨ s.pc=2555 ∨ s.pc=2337 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem dispatch_pcs (s : Dispatch.Site) (h : s.pc ∈ Lib.requestPcs)
    (a : s≠.loaderEntry) (b : s≠.mmaEntry) :
    s.pc=2337 ∨ (s.pc=2333 ∧ s=.idleDec) ∨ (s.pc=2336 ∧ s=.idleInc) := by
  revert h a b
  cases s <;> decide

/-- **The position of a worker's request is its warp's**: warps 4 and 5 take the idle sites, warp 6
the loader's and warp 7 the MMA's. -/
theorem worker_request_warp {pc inc n inst} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) (hw : 128≤g%L.block) :
    pc=2337 ∨ ((pc=2333 ∨ pc=2336) ∧ g%L.block/32<6) ∨ ((pc=2344 ∨ pc=2420) ∧ g%L.block/32=6) ∨
      ((pc=2422 ∨ pc=2555) ∧ g%L.block/32=7) := by
  have len := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨⟨s0,n0⟩,hs,tab,pcs,_,grp⟩ := request_state hp hX hf words he
  have hit : pc ∈ Lib.requestPcs := request_mem hX he
  rcases s0 with s0 | ⟨r,s0⟩
  · rcases grp with ⟨h,_⟩ | ⟨h,_⟩ <;> exact h.elim
  rcases r with r | r
  · cases r with
    | prologue w =>
      have : g%L.block<128 := data_warp hp hX len hs
      omega
    | dispatch w x =>
      rcases s0 with d | ⟨i,d⟩
      · obtain ⟨idle,ne1,ne2⟩ := idle_warp hp hX words len hs
        change d.site.pc=pc at pcs
        rcases dispatch_pcs d.site (pcs ▸ hit) ne1 ne2 with h | ⟨h,i⟩ | ⟨h,i⟩
        · exact .inl (pcs ▸ h)
        · exact .inr (.inl ⟨.inl (pcs ▸ h),idle (.inl i)⟩)
        · exact .inr (.inl ⟨.inr (pcs ▸ h),idle (.inr (.inr (.inr i)))⟩)
      · cases i with
        | loader _ =>
          have w6 : g%L.block/32=6 := tab.2.1
          change d.site.pc=pc at pcs
          rcases loader_pcs d.site (pcs ▸ hit) with h | h | h
          · exact .inr (.inr (.inl ⟨.inl (pcs ▸ h),w6⟩))
          · exact .inr (.inr (.inl ⟨.inr (pcs ▸ h),w6⟩))
          · exact .inl (pcs ▸ h)
        | mma _ =>
          have w7 : g%L.block/32=7 := tab.2.1
          change d.site.pc=pc at pcs
          rcases mma_pcs d.site (pcs ▸ hit) with h | h | h
          · exact .inr (.inr (.inr ⟨.inl (pcs ▸ h),w7⟩))
          · exact .inr (.inr (.inr ⟨.inr (pcs ▸ h),w7⟩))
          · exact .inl (pcs ▸ h)
  · rcases grp with ⟨h,_⟩ | ⟨h,_⟩ <;> exact h.elim

/-- **The direction and count of a request are its instruction's.** -/
theorem request_value {pc inc n inst} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) : Lib.requestAt pc = some (inc,n) := by
  obtain ⟨_,bad⟩ | ⟨t,ins,o,_,code,fire⟩ := get_source hX he
  · cases bad
  have := EventFrame.fires_source_pc fire
  exact (Lib.request_fires code fire).2 inc n inst rfl

/-- **An exit follows three barrier-1 events of its thread.** -/
theorem exit_barriers {pc} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (he : X.get (g,k)=some ⟨pc,.exit⟩) :
    3≤((X.tr g).take k).countP (Execution.isBarId 1) := by
  have led := ledger_event hp hX words he (fun _ => nofun)
  obtain ⟨_,bad⟩ | ⟨_,_,_,_,code,fire⟩ := get_source hX he
  · cases bad
  have site := Lib.ret_pc' code fire rfl
  obtain rfl : pc=2855 := by simpa [Lib.retPcs] using site
  have h : Lib.ledgerOk 2855 (((X.tr g).take k).countP (Execution.isBarId 1))
      (((X.tr g).take k).countP SetMaxNReg.isRequest) = true := led
  have last := (Bool.and_eq_true_iff.mp h).2
  simpa using last

/-- No request is the fifth of its thread: the ledger has no position for ordinal 4. -/
private theorem request_ne_four {pc inc n inst} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) :
    ((X.tr g).take k).countP SetMaxNReg.isRequest ≠ 4 := by
  intro four
  have led := ledger_event hp hX words he (fun _ => nofun)
  have hit := request_mem hX he
  rw [four] at led
  simp only [Lib.requestPcs,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Lib.ledgerOk,Lib.requestPcs] at led

/-- **A thread makes at most four requests**: every request is one of the first four. -/
theorem request_le_three {pc inc n inst} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) :
    ((X.tr g).take k).countP SetMaxNReg.isRequest ≤ 3 := by
  by_contra big
  have ne := request_ne_four hp hX words he
  obtain ⟨j,x,hj,hx,hcount⟩ := PTX.CtaBarrier.countP_index (xs := (X.tr g).take k)
    (p := SetMaxNReg.isRequest) (n := 4) (by omega)
  have jk : j<k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt jk] at hj
  rw [List.take_take,Nat.min_eq_left jk.le] at hcount
  obtain ⟨px,kx⟩ := x
  obtain ⟨inc',n',inst',rfl⟩ : ∃ inc n inst, kx = .setMaxReg inc n inst := by
    cases kx <;> simp_all [SetMaxNReg.isRequest]
  exact request_ne_four hp hX words (show X.get (g,j)=some _ from hj) hcount

/-- **A request is at its warp's position for its ordinal**, the ordinal at most 2 in the default
partition and 3 in a worker. -/
theorem request_pc {pc inc n inst} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨pc,.setMaxReg inc n inst⟩) :
    pc=Lib.reqPcOf (g%L.block/32) (((X.tr g).take k).countP SetMaxNReg.isRequest) ∧
      (g%L.block<128 → ((X.tr g).take k).countP SetMaxNReg.isRequest ≤ 2) ∧
      (128≤g%L.block → ((X.tr g).take k).countP SetMaxNReg.isRequest ≤ 3) := by
  have hb : L.block=256 := hp.block
  have led := ledger_event hp hX words he (fun _ => nofun)
  have three := request_le_three hp hX words he
  generalize ((X.tr g).take k).countP SetMaxNReg.isRequest = r at led three ⊢
  rcases request_group hp hX hf words he with ⟨low,dq⟩ | ⟨high,wq⟩
  · have w4 : g%L.block/32<4 := by omega
    simp only [Lib.dataReq,Bool.or_eq_true,beq_iff_eq] at dq
    rcases dq with (rfl|rfl)|rfl <;>
      simp_all [Lib.ledgerOk,Lib.requestPcs,Lib.reqPcOf]
  · have w4 : ¬ g%L.block/32<4 := by omega
    have w8 : g%L.block/32<8 := by
      have := Nat.mod_lt g (show L.block>0 by omega)
      omega
    refine ⟨?_,fun h => by omega,fun _ => three⟩
    simp only [Lib.reqPcOf,w4,↓reduceIte]
    rcases worker_request_warp hp hX hf words he high with rfl | ⟨pcs,w⟩ | ⟨pcs,w⟩ | ⟨pcs,w⟩ <;>
      first
      | (rcases pcs with rfl | rfl <;>
          simp_all [Lib.ledgerOk,Lib.requestPcs] <;> split_ifs <;> omega)
      | (simp_all [Lib.ledgerOk,Lib.requestPcs])

private theorem startup_ne (s : Startup.Site) : s.pc≠2855 := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem loader_ne (s : Loader.Site) : s.pc≠2855 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_ne (s : Mma.Site) : s.pc≠2855 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epilogue_exit (s : Epilogue.Site) (h : s.pc=2855) : Epilogue.requestPhase s=3 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem dispatch_ret (s : Dispatch.Site) (h : s.pc=2855) : s=.ret := by
  revert h
  cases s <;> decide

/-- **An exiting thread has made its requests**: three in the default partition, four in a
worker. -/
theorem exit_requests {pc} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (he : X.get (g,k)=some ⟨pc,.exit⟩) :
    (g%L.block<128 → 3≤((X.tr g).take k).countP SetMaxNReg.isRequest) ∧
      (128≤g%L.block → 4≤((X.tr g).take k).countP SetMaxNReg.isRequest) := by
  have len := (List.getElem?_eq_some_iff.mp he).1.le
  have site : pc=2855 := by
    obtain ⟨_,bad⟩ | ⟨_,_,_,_,code,fire⟩ := get_source hX he
    · cases bad
    simpa [Lib.retPcs] using Lib.ret_pc' code fire rfl
  obtain ⟨⟨s0,n0⟩,hs,tab,ok,pcs,count⟩ := event_state hp hX hf words he (fun _ => nofun)
  rw [← count]
  rcases s0 with s0 | ⟨r,s0⟩
  · exact absurd (pcs.trans site) (startup_ne _)
  rcases r with r | r
  · cases r with
    | prologue w =>
      have low : g%L.block<128 := data_warp hp hX len hs
      refine ⟨fun _ => ?_,fun h => by omega⟩
      rcases s0 with d | ⟨ent,d | ⟨u,d⟩⟩
      · have := d.site.pc_range
        change d.site.pc=pc at pcs
        omega
      · have := d.site.pc_range
        change d.site.pc=pc at pcs
        rcases this with h | h
        · omega
        · have e : (Softmax.Site.epilogue).pc=2565 := rfl
          rw [h] at pcs
          omega
      · change Epilogue.requestPhase d.site ≥ 3
        change d.site.pc=pc at pcs
        rw [epilogue_exit d.site (pcs.trans site)]
    | dispatch w x =>
      have high : 128≤g%L.block := (worker_warp hp hX len hs).1
      refine ⟨fun h => by omega,fun _ => ?_⟩
      rcases s0 with d | ⟨i,d⟩
      · change d.site.pc=pc at pcs
        obtain ⟨_,_,_,late⟩ := ok
        have := late (by rw [dispatch_ret d.site (pcs.trans site)]; exact .inr (.inr rfl))
        change 4 ≤ 3*d.round + Dispatch.requestOffset d.site
        rw [dispatch_ret d.site (pcs.trans site)]
        change 4 ≤ 3*d.round + 1
        omega
      · cases i with
        | loader _ => exact absurd (pcs.trans site) (loader_ne _)
        | mma _ => exact absurd (pcs.trans site) (mma_ne _)
  · exact ok.elim

end PTX.Kernels.InklingRelDecode.Proof.Export
