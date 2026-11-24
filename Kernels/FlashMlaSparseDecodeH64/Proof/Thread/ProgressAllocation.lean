-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueAllocationTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.Assumptions
public import Lemmas.Step.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Clc.ClcExecution
import Lemmas.Tmem.AllocResult
import Lemmas.Tmem.TmemResourceReady
import Lemmas.Flow.AllocTmpl
import Lemmas.Step.Issue
import Lemmas.Step.ReadSource
import Lemmas.Tmem.Alloc512

public section

/-! # Progress at the local allocation-result store -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation

open PTX PTX.Flow PTX.Proof Tmem.Pair

private theorem alloc_store_previous {L : Launch} {g : Nat} {s : Site} {e : Event}
    (h : Proof.next L g s e = some (some .allocStore)) :
    s = .alloc ∧ ∃ grp dst count, e.kind = .tc (.resource grp dst (.alloc count)) := by
  cases s <;> simp only [Proof.next] at h
  case' alloc =>
    split at h
    · rename_i grp dst count he
      exact ⟨rfl, grp, dst, count, he⟩
    · cases h
  all_goals repeat' split at h
  all_goals cases h

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- At the result store, the previous event is the lane's actual allocation request. -/
theorem alloc_store_predecessor {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue .allocStore))) :
    ∃ tag, X.get (g, (X.tr g).length - 1) =
      some ⟨tag, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩ := by
  have hPos : 0 < (X.tr g).length := by
    by_contra! h
    rw [show (X.tr g).length = 0 by omega, Frame.stateAt_zero] at hState
    cases hState
  let i := (X.tr g).length - 1
  have hIndex : i + 1 = (X.tr g).length := by dsimp [i]; omega
  obtain ⟨s, e, he, hS, hNext⟩ := PrologueRoleTrace.previous_prologue
    (i := i) (by rw [hIndex]) (hIndex.symm ▸ hState)
  obtain ⟨rfl, grp, dst, count, hKind⟩ := alloc_store_previous hNext
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at he hS
  cases ResourceEvents.emits hpre hf hKind with
  | alloc hGrp hDst hCount =>
    obtain ⟨tag, kind⟩ := e
    subst grp dst
    cases hCount
    change kind = _ at hKind
    subst kind
    exact ⟨tag, he⟩

/-- The released representative lane can write the zero column selected by the safe allocator.
The extension preserves the resource result rule and every kernel assumption. -/
theorem alloc_store_extension {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (hub : ¬ HasUb X) (hresource : ¬ Tmem.Pair.ResourceUnsafe L X) (hp : Frame.Pending L X g)
    (hrel : PTX.Step.Released L X g)
    (hstate : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue .allocStore)))
    (halloc : ∃ site, X.get (g, (X.tr g).length - 1) =
      some ⟨site, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨site, hprev⟩ := halloc
  have hne : X.tr g ≠ [] := by
    intro hn
    simp [Execution.get, hn] at hprev
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, hat, _, hc, hout⟩ := Frame.end_at hs hp.1 hr hstate
  change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have ha : u.regs 554 = some (b32 (allocAddress L g).addr) :=
    holds_mem hat.2.2.2.2 (mem_factsFrom (by table_decide : 554 ∈ liveAll 91))
  have hn : u.regs 555 = some (b32 512) :=
    holds_mem hat.2.2.2.2 (mem_factsFrom (by table_decide : 555 ∈ liveAll 91))
  have hsub : u.sub = 1 := hat.2.1
  have hal := hpre.sharedAlignment
  rw [← hpre.sharedBase] at hal
  have hbound := sharedBase_lt hpre
  have hfit : (allocAddress L g).addr < 2 ^ 32 := by
    change L.sharedBase + 222752 < 2 ^ 32
    omega
  have halign : (allocAddress L g).addr % 4 = 0 := by
    change (L.sharedBase + 222752) % 4 = 0
    omega
  rw [tcAlloc_tmpl1 hb ha hfit halign hn hsub] at hout
  let dst := allocAddress L g
  let e : Event := ⟨u.pc, .wr { loc := dst, size := 4 } (b32 0).toBytes⟩
  have hresult : Tmem.Pair.ResultOk L (X.snoc g e (fun _ => none)) := by
    apply hX.tmemPairResult.snoc
    intro q a bytes he _ q' group addr count hget cta record base hrec _ haction
    simp only [e, Event.mk.injEq, Kind.wr.injEq] at he
    obtain ⟨_, _, rfl⟩ := he
    rw [hprev] at hget
    have hcount : count = 512 := by
      have h := Kind.tc.inj (congrArg Event.kind (Option.some.inj hget))
      exact (Tmem.Request.alloc.inj (TcKind.resource.inj h).2.2).symm
    subst count
    rw [hX.alloc512_base (tmemNoFault_of_safe hresource cta) hrec haction]
    rfl
  exact PTX.Step.plain_counted_extension hX hp.1 (.inl hne) hrel hr hτ
    (e := e) (o := some { u with pc := u.pc + 1, sub := 0 })
    ⟨_, hout, 0, by decide, rfl, rfl⟩ rfl (by simp [e, Kind.isTma])
    (by simp [e]) (by simp [e]) (by simp [e]) rfl hresult
    (Interface.all_wf_snoc_of_not_nc hX (by simp [e]) (by simp [e]))

/-- A released lane at the allocation read-back can issue its ordinary shared load. -/
theorem alloc_read_extension {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (hub : ¬ HasUb X) (hguarded : SyncGuarded L kernel X) (hp : Frame.Pending L X g)
    (hrel : PTX.Step.Released L X g)
    (hstate : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue .allocRead))) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil, Frame.stateAt_zero] at hstate
    cases hstate
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, hat, _, hcode, hout⟩ := Frame.end_at hs hp.1 hr hstate
  change kernel.code[Flow.load_0]? = some ins at hcode
  obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_load_0)
  change out kernel Assumptions.all L g u =
    .ev (eventTmpl Assumptions.all L g u (.mem allocLoad)) at hout
  rw [alloc_read_template hpre hat.2.1] at hout
  exact PTX.Step.read_source_counted_extension hX hp.1 hne hrel hr hτ hout
    (fun _ _ _ => Interface.all_wf_snoc_of_not_nc hX (by simp) (by simp)) hguarded

/-- A performed allocation has published its result or its released representative can do so. -/
theorem result_or_representative {i : EvId} {tag : Nat} {dst : Option Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) (hSafe : ¬ Tmem.Pair.ResourceUnsafe L X)
    (he : X.get i = some ⟨tag, .tc (.resource .one dst (.alloc 512))⟩)
    (hCovered : Tmem.Pair.Covered L X i) :
    (∃ store obj, AllocResult L X store i obj) ∨
    ∃ g, Frame.Pending L X g ∧ PTX.Step.Released L X g ∧
      Frame.stateAt (Machine.code P L) X g (X.tr g).length =
        some (some (.prologue .allocStore)) := by
  obtain ⟨ws, hws, w, hw, lane, hLane⟩ := hCovered
  obtain ⟨grp, hv⟩ := hws.valid hX.tmemPair hw
  have hReq := hv.2.2.1 lane
  rw [hLane, he] at hReq
  have hArgs := TcKind.resource.inj (Kind.tc.inj (congrArg Event.kind (Option.some.inj hReq)))
  have hGroup : grp = .one := hArgs.1.symm
  have hAlloc : w.request = .alloc 512 := hArgs.2.2.symm
  let g := (w.event L 0).1
  let j := (w.event L 0).2
  have hLead : X.get (g, j) = some ⟨w.pc, .tc (.resource .one w.dst (.alloc 512))⟩ := by
    simpa only [hGroup, hAlloc] using hv.2.2.1 0
  have hg : g < L.threads := Frame.lt_of_get hX hLead
  have hZero : PTX.laneOf L g = 0 := by
    have hLt : w.warp * 32 < L.block := by have := hv.2.1; omega
    simp only [g, PTX.laneOf, Tmem.Pair.WarpRequest.event, Fin.val_zero, Nat.add_zero]
    rw [Nat.mul_comm w.cta, Nat.mul_add_mod, Nat.mod_eq_of_lt hLt]
    simp
  have hLocalZero : laneOf L g = 0 := (laneOf_core hpre).symm.trans hZero
  obtain ⟨d, o, hAt, hFired⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht hLead
    (by simp)
  have hShape := ResourceEvents.emits hpre hFired rfl
  have hClass : d = .prologue .alloc ∧ w.dst = some (allocAddress L g) := by
    cases hShape
    case alloc _ hDst _ => exact ⟨rfl, hDst⟩
    all_goals contradiction
  obtain ⟨rfl, hDst⟩ := hClass
  have hSucc : Frame.stateAt (Machine.code P L) X g (j + 1) =
      some (some (.prologue .allocStore)) := by
    rw [Frame.stateAt_succ hLead, hAt]
    change Machine.next P L g (.prologue .alloc)
      ⟨w.pc, .tc (.resource .one w.dst (.alloc 512))⟩ = _
    simp only [Machine.next, Proof.next, hLocalZero, ↓reduceIte]
    rfl
  have hj : j < (X.tr g).length := PTX.len_of_get hLead
  by_cases hMore : j + 1 < (X.tr g).length
  · left
    have hStore : X.get (g, j + 1) = some (X.tr g)[j + 1] := List.getElem?_eq_getElem hMore
    obtain ⟨t, hStore'⟩ := alloc_write hpre hX hs hSafe hLocalZero hAt hLead hStore
    have hTag : t = w.pc := by
      obtain ⟨_, _, _, _, _, _, hFire⟩ := Frame.fired_site hs hX hLead hAt
      obtain ⟨_, _, _, _, _, _, hFire'⟩ := Frame.fired_site hs hX hStore' hSucc
      exact (fires_pc hFire').trans (fires_pc hFire).symm
    subst t
    have hOwner : (allocAddress L g).cta = w.cta :=
      (Tmem.Pair.WarpRequest.event_props hv 0).1
    refine ⟨(g, j + 1), allocAddress L g, ?_⟩
    rw [← hLane]
    exact AllocResult.of_warpRequest hv hAlloc hDst rfl hOwner hStore' lane
  · right
    have hLast : (X.tr g).length - 1 = j := by omega
    have hCover : Tmem.Pair.Covered L X (g, j) := ⟨ws, hws, w, hw, 0, rfl⟩
    have hReady := Tmem.Pair.ReturnReady.ready hX.tmemPair hLead
      ⟨hCover.performed hX.tmemPair, fun _ => hCover⟩
      (fun _ _ hn => (hn hZero).elim)
    have hRel : PTX.Step.Released L X g := ⟨fun _ _ _ _ => by rw [hLast]; exact hReady⟩
    have hp : Frame.Pending L X g := by
      refine ⟨hg, ?_, ?_⟩
      · rintro ⟨_, _, hCanceled⟩
        obtain ⟨k, sp, tg, _, hIssue, _⟩ := hX.clc.canceled_has_issue hCanceled
        exact GlobalWrites.no_clc (i := k) (s := sp) (tg := tg) hX hIssue
      · intro t hExit
        rw [List.getLast?_eq_getElem?, hLast] at hExit
        exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hLead.symm.trans hExit)))
    exact ⟨g, hp, hRel, (show (X.tr g).length = j + 1 by omega) ▸ hSucc⟩


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
