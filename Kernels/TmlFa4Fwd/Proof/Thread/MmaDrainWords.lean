-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScanLaunchFrame
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import all Kernels.TmlFa4Fwd.Proof.MmaRoleSetup
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

def drainRoots (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1180,b32 (laneOf l g)),(7506,b64 p.cuQBase),(1072,b32 (g/l.block))]

set_option maxRecDepth 100000 in
private theorem drainKeptCode :
    ((kernel.code.drop 1981).take (2768-1981)).all
      (fun i => [1180,7506,1072].all (fun r => !(mmaWrites i.op).contains r)) = true := by
  kernel_rfl

variable {p : Params} {l : Launch}

theorem preserveDrainRoots {g : Nat} {s u : TState} {ev : Option Event} (hl : 1981 ≤ s.pc)
    (hh : s.pc < 2768) (he : WStep kernel Assumptions.all l g s ev u)
    (hs : Holds s.regs (drainRoots p l g)) : Holds u.regs (drainRoots p l g) := by
  apply holdsSchedulerFrame (regs := [1180,7506,1072]) hs
  · intro r hr
    apply mmaStepReg (by omega) hh _ he
    intro i hi
    have h := List.all_eq_true.mp drainKeptCode i (by
      apply List.mem_of_getElem? (i := s.pc-1981)
      rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hl])
    simpa using List.all_eq_true.mp h r hr
  · intro pair hPair
    simpa [drainRoots] using List.mem_map_of_mem (f := Prod.fst) hPair

def knownFloors (floor : Nat) : Prop :=
  (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true ∧
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true

set_option maxRecDepth 100000 in
private theorem firstSearchFloor : knownFloors 1981 := by
  exact ⟨by kernel_rfl,by kernel_rfl⟩

set_option maxRecDepth 100000 in
private theorem firstDrainEndFloor : knownFloors 2654 := by
  exact ⟨by kernel_rfl,by kernel_rfl⟩

set_option maxRecDepth 100000 in
private theorem earlyExitFloor : knownFloors 2763 := by
  exact ⟨by kernel_rfl,by kernel_rfl⟩

private theorem floorOfPath {floor : Nat} (hFloor : knownFloors floor)
    {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u) (hs : floor ≤ s.pc) :
    floor ≤ u.pc := by
  induction h with
  | refl => exact hs
  | tau he _ ih => exact ih (eventTailStepOfAudit hFloor.1 hFloor.2 hs (.inl ⟨rfl,he⟩))
  | event he _ ih => exact ih (eventTailStepOfAudit hFloor.1 hFloor.2 hs (.inr ⟨_,rfl,he⟩))

private theorem sourceRegionBeforeDrain {pc : Nat} (hLo : 1981 ≤ pc) (hHi : pc < 2647) :
    ∃ r : Fin 12, (roleRegion r).lo ≤ pc ∧ pc < (roleRegion r).hi := by
  by_cases h0 : pc < 1985
  · exact ⟨0,by change 1907 ≤ pc; omega,h0⟩
  by_cases h8 : pc < 1988
  · exact ⟨8,Nat.le_of_not_gt h0,h8⟩
  by_cases h1 : pc < 2042
  · exact ⟨1,Nat.le_of_not_gt h8,h1⟩
  by_cases h2 : pc < 2286
  · exact ⟨2,Nat.le_of_not_gt h1,h2⟩
  by_cases h9 : pc < 2291
  · exact ⟨9,Nat.le_of_not_gt h2,h9⟩
  by_cases h3 : pc < 2534
  · exact ⟨3,Nat.le_of_not_gt h9,h3⟩
  exact ⟨4,Nat.le_of_not_gt h3,hHi⟩

private theorem drainEntryStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 1981 ≤ s.pc) (hHi : s.pc < 2647) (hShape : RoleShape s)
    (he : WStep kernel Assumptions.all l g s ev u) :
    1981 ≤ u.pc ∧ (u.pc ≤ 2647 ∨ 2763 ≤ u.pc) ∧ RoleShape u := by
  obtain ⟨r,hl,hh⟩ := sourceRegionBeforeDrain hLo hHi
  obtain ⟨hBound,hU⟩ := roleRegionStep r hl hh hShape he
  refine ⟨eventTailStepOfAudit firstSearchFloor.1 firstSearchFloor.2 hLo he,?_,hU⟩
  fin_cases r <;> simp only [roleRegion,List.mem_cons,List.not_mem_nil,or_false]
    at hl hh hBound <;> omega

private theorem pathToDrainEntry {g : Nat} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u) (hs : 1981 ≤ s.pc ∧ s.pc ≤ 2647)
    (hShape : RoleShape s) (hRegs : Holds s.regs (drainRoots p l g))
    (hu : 2647 ≤ u.pc ∧ u.pc < 2763) :
    ∃ mid pre tail, events = pre ++ tail ∧ mid.pc = 2647 ∧ RoleShape mid ∧
      Holds mid.regs (drainRoots p l g) ∧
      TraceReach kernel Assumptions.all l g s pre mid := by
  have step {a b : TState} {e : Option Event} {rest : List Event}
      (ha : 1981 ≤ a.pc) (hb : a.pc < 2647) (hS : RoleShape a)
      (hF : Holds a.regs (drainRoots p l g)) (he : WStep kernel Assumptions.all l g a e b)
      (hTail : TraceReach kernel Assumptions.all l g b rest u) :
      (1981 ≤ b.pc ∧ b.pc ≤ 2647) ∧ RoleShape b ∧ Holds b.regs (drainRoots p l g) := by
    obtain ⟨hB,hBound,hT⟩ := drainEntryStep ha hb hS he
    have hLater : ¬ 2763 ≤ b.pc := fun h =>
      (Nat.not_le_of_gt hu.2) (floorOfPath earlyExitFloor hTail h)
    exact ⟨⟨hB,hBound.resolve_right hLater⟩,hT,preserveDrainRoots ha (by omega) he hF⟩
  induction h with
  | refl s =>
    exact ⟨s,[],[],rfl,by omega,hShape,hRegs,.refl _⟩
  | @tau a b c es he ht ih =>
    by_cases hz : a.pc = 2647
    · exact ⟨a,[],es,rfl,hz,hShape,hRegs,.refl _⟩
    obtain ⟨hb,hBS,hBR⟩ := step hs.1 (by omega) hShape hRegs (.inl ⟨rfl,he⟩) ht
    obtain ⟨mid,pre,tail,hSplit,hPc,hS,hR,hPath⟩ := ih hb hBS hBR hu step
    exact ⟨mid,pre,tail,hSplit,hPc,hS,hR,.tau he hPath⟩
  | @event a b c es e he ht ih =>
    by_cases hz : a.pc = 2647
    · exact ⟨a,[],e::es,rfl,hz,hShape,hRegs,.refl _⟩
    obtain ⟨hb,hBS,hBR⟩ := step hs.1 (by omega) hShape hRegs (.inr ⟨_,rfl,he⟩) ht
    obtain ⟨mid,pre,tail,hSplit,hPc,hS,hR,hPath⟩ := ih hb hBS hBR hu step
    exact ⟨mid,e::pre,tail,congrArg (List.cons e) hSplit,hPc,hS,hR,.event he hPath⟩

theorem drainStartOfObservedEvent {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g j : Nat}
    {e : Event} (he : X.get (g,j) = some e) (hLate : 2647 ≤ e.pc) (hEarly : e.pc < 2763)
    (hHint : e.pc ∉ registerHintSites) (hOrdinary : ∀ f, e.kind ≠ .ub f) :
    ∃ pos ≤ j, ∃ s ending, At s 2647 (drainRoots p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending := by
  have hg := event_thread_lt hMax.1 he
  have hw := mmaRoleEventWarp hp hMax.1 he (by omega) (by omega) hHint
  obtain ⟨i,b,t,ending,hB,_,hSite,_,ht,_,hr⟩ := firstGroupScanLaunchFrame hp hMax hg hw hCuQ
  have hj : i+1 ≤ j := Nat.succ_le_of_lt (traceOrderOfPcFloor hMax.1
    firstSearchFloor.1 firstSearchFloor.2 hB he (by omega) (by omega))
  have hGet : ((X.tr g).drop (i+1))[j-(i+1)]? = some e := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  obtain ⟨t',_,hPath,hFire⟩ := hr.before_event hGet
  have ht' : t'.pc = e.pc := (estep_source_pc hFire).symm
  have hFrame : Holds t.regs (drainRoots p l g) := by
    refine ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl,trivial⟩
  obtain ⟨s,pre,tail,hSplit,hPc,hShape,hRegs,hPrefix⟩ := pathToDrainEntry hPath
    (by rw [ht.1]; decide) ⟨by rw [ht.2.1]; decide,ht.2.2.1,fun _ => ht.2.1⟩ hFrame
    (by omega)
  have hN := congrArg List.length hSplit
  have hBefore : i+1+pre.length ≤ j := by
    simp only [List.length_take,List.length_append] at hN
    omega
  have hFront : ((X.tr g).drop (i+1)).take pre.length = pre := by
    have hBound : pre.length ≤ j-(i+1) := by omega
    have h := congrArg (fun xs : List Event => xs.take pre.length) hSplit
    rw [List.take_take,Nat.min_eq_left hBound,List.take_left' rfl] at h
    exact h
  have hTrace : (X.tr g).drop (i+1) = pre ++ (X.tr g).drop (i+1+pre.length) := by
    have h := (List.take_append_drop pre.length ((X.tr g).drop (i+1))).symm
    rw [hFront,List.drop_drop] at h
    simpa only [Nat.add_comm] using h
  obtain ⟨before,hBack,hLocal⟩ := hPrefix.returnedPrefix
  have hSeen : ((X.tr g).drop (i+1+pre.length))[j-(i+1+pre.length)]? = some e := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
    exact he
  have hNotEmpty : (X.tr g).drop (i+1+pre.length) ≠ [] :=
    fun h => by simp [h] at hSeen
  have hTail := (hBack.after_returned_prefix (hTrace ▸ hr)).after_local_nonempty hLocal hNotEmpty
  have hFault : s.fault = none := by
    cases h : s.fault with
    | none => rfl
    | some f =>
      exact (hOrdinary f (hTail.eventOfFault h hSeen)).elim
  exact ⟨_,hBefore,s,ending,⟨hPc,hShape.2.2 (by omega),hShape.2.1,hFault,hRegs⟩,hTail⟩

theorem signedWord {n : Nat} (h : n < 2^31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned,toNat_ofNat_lt (show n < 2^64 by omega),
    Nat.mod_eq_of_lt (show n < 2^32 by omega),ite_eq_left h]

theorem firstDrainBatch {m : Mem0} (hp : Pre p l m) {g : Nat} {s : TState}
    (hs : At s 2647 (drainRoots p l g)) :
    ∃ u, run kernel Assumptions.all l g 1 s = some u ∧
      At u 2648 ((7149,b32 p.batch)::drainRoots p l g) := by
  let u := next (setReg s 7149 (b32 p.batch))
  obtain ⟨hBound,hParam⟩ := hp.values (19,p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [param19_name] at hParam
  have hCore : run kernel [] l g 1 s = some u := by
    apply run_local Flow.code_2647 rfl hs
    rw [execLocalA_nil,execLocal_mem rfl]
    simp only [execMove,MemAccess.regs,List.filterMap_cons,List.filterMap_nil,id_eq,hParam,
      DType.width,MemExt.extendBits_same,pure,Except.pure,truncBits_ofNat hBound (by decide)]
    rfl
  exact ⟨u,localRun (pc := 2647) (n := 1) (by decide) (by decide) hs.1 rfl hCore,
    hs.set (by simp [drainRoots])⟩

/-- The initial drain initializes its CuQ word and branches around the load beyond the table. -/
theorem firstDrainGateWithZero {m : Mem0} (hp : Pre p l m) {g : Nat} {s : TState}
    (hs : At s 2647 (drainRoots p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if p.batch < laneOf l g then 2654 else 2651)
        ((7209,b32 0)::(7149,b32 p.batch)::drainRoots p l g) := by
  let lane := laneOf l g
  let F := drainRoots p l g
  have hl : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨t,hLoad,ht⟩ := firstDrainBatch hp hs
  have hBatch := hp.shape.2.1
  have hGuard : Seg kernel [] l g 2 2648 ((7149,b32 p.batch)::F) 2650
      ((410,.pred (decide (p.batch < lane)))::(7209,b32 0)::(7149,b32 p.batch)::F) := by
    intro v hv
    dsimp [F,drainRoots] at hv ⊢
    seg_fp hv using
      try simp only [truncBits_ofNat (show laneOf l g < 2^32 by omega) (by decide),
      truncBits_ofNat (show p.batch < 2^32 by omega) (by omega), compare, Option.getD_some,
      signedWord (show laneOf l g < 2^31 by omega), signedWord (show p.batch < 2^31 by omega),
        gt_iff_lt,Int.ofNat_lt]
      rfl
  obtain ⟨v,hGuardRun,hV⟩ := hGuard t ht
  obtain ⟨u,hBranch,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2650 _ hV hV.2.2.2.2.1 (by simp)
  have h1 := localRun (pc := 2648) (n := 2) (by decide) (by decide) ht.1
    (by decide +kernel) hGuardRun
  have h2 := localRun (pc := 2650) (n := 1) (by decide) (by decide) hV.1 rfl hBranch
  exact ⟨u,(run_rtg hLoad).trans ((run_rtg h1).trans (run_rtg h2)),by
    simpa only [decide_eq_true_eq] using hU.mono hU.2.2.2.2.2⟩

private theorem firstDrainGate {m : Mem0} (hp : Pre p l m) {g : Nat} {s : TState}
    (hs : At s 2647 (drainRoots p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if p.batch < laneOf l g then 2654 else 2651) (drainRoots p l g) := by
  obtain ⟨u,hPath,hu⟩ := firstDrainGateWithZero hp hs
  exact ⟨u,hPath,hu.mono hu.2.2.2.2.2.2⟩

/-- The in-range first drain lane computes the actual CuQ scalar address. -/
theorem firstDrainAddress {m : Mem0} (hp : Pre p l m) {g : Nat} (hb : laneOf l g ≤ p.batch) :
    Seg kernel [] l g 2 2651 (drainRoots p l g) 2653
      [(7884,b64 (p.cuQBase+4*laneOf l g))] := by
  intro t ht
  have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRange
  have hl : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hL32 : laneOf l g < 2^32 := by omega
  have hL64 : laneOf l g < 2^64 := by omega
  have hOff : 4*laneOf l g < 2^64 := by omega
  have hBase : p.cuQBase < 2^64 := by omega
  have hAddr : p.cuQBase+4*laneOf l g < 2^64 := by omega
  have h4 : (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 := rfl
  unfold drainRoots at ht
  seg_fp ht using simp only [b64,kind_u_beq_s,Bool.false_eq_true,↓reduceIte,
    truncBits_ofNat hL32 (by decide),toNat_ofNat_lt hL64,h4,Nat.mul_comm (laneOf l g),
    truncBits_ofNat hOff (by decide),truncBits_ofNat hBase (by decide),
    ← BitVec.ofNat_add,truncBits_ofNat hAddr (by decide)]

private theorem firstDrainReadOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g j : Nat}
    {a : Acc} {bytes : List (Option Byte)} (he : X.get (g,j) = some ⟨2653,.rd a bytes⟩) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  obtain ⟨pos,hPos,t,ending,ht,hr⟩ := drainStartOfObservedEvent hp hMax hCuQ he
    (show 2647 ≤ 2653 by decide) (show 2653 < 2763 by decide)
    (show 2653 ∉ registerHintSites by decide) (by intro f h; cases h)
  obtain ⟨s,hLocal,hs⟩ := firstDrainGate hp ht
  have hFloor {s : TState} {es : List Event} {o : Option TState} (hPc : 2654 ≤ s.pc)
      (hRun : Run kernel Assumptions.all l g s es o) : ∀ e ∈ es, 2654 ≤ e.pc := by
    obtain ⟨_,hw⟩ := walkFromRun hRun
    exact eventTailEvents firstDrainEndFloor.1 firstDrainEndFloor.2 hw hPc
  by_cases hi : laneOf l g ≤ p.batch
  · have hs' : At s 2651 (drainRoots p l g) := by
      simpa only [ite_eq_right (Nat.not_lt_of_ge hi)] using hs
    obtain ⟨v,hMove,hv⟩ := firstDrainAddress hp hi s hs'
    have hRun := localRun (pc := 2651) (n := 2) (by decide) (by decide) hs'.1
      (by decide +kernel) hMove
    let acc : Acc := {loc := globalLoc (p.cuQBase+4*laneOf l g),size := 4}
    have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRange
    have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
    have hOut : out kernel Assumptions.all l g v = .ev (.read acc (afterLoad v [7209])) := by
      rw [out_eq_core (by rw [hv.1]; decide) (by rw [hv.1]; decide)]
      rw [out_event hv.2.2.2.1 (by rw [hv.1]; exact Flow.code_2653) rfl rfl]
      change Out.ev (loadTmpl [] l g v .global false 32 [7209] 7884 0) = _
      exact congrArg Out.ev (loadTmpl_global hv.2.1 hv.2.2.2.2.1 (by omega)
        (by decide) (by omega))
    let hn : Next kernel Assumptions.all l g t v (.read acc (afterLoad v [7209])) :=
      ⟨hLocal.trans (run_rtg hRun),hOut⟩
    exact ⟨_,hi,(hn.uniqueScalarReadAt hv.1 hr hPos he (fun _ _ hp => hFloor hp)).2⟩
  · have hs' : s.pc = 2654 := by simpa only [ite_eq_left (Nat.lt_of_not_ge hi)] using hs.1
    have hGet : ((X.tr g).drop pos)[j-pos]? = some ⟨2653,.rd a bytes⟩ := by
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
      exact he
    have hMore : (X.tr g).drop pos ≠ [] := fun h => by simp [h] at hGet
    exact (Nat.not_le_of_gt (by decide : 2653 < 2654)
      (hFloor hs'.ge (hr.after_local_nonempty hLocal hMore) _ (List.mem_of_getElem? hGet))).elim

/-- The opening lookup of the MMA drain uses one CuQ word from the launch records. -/
@[no_expose] def MmaInitialDrainCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop := X.get i = some ⟨2653,.rd a bytes⟩

def MmaInitialDrainAddresses (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, MmaInitialDrainCuQRead X i a bytes →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4}

theorem MmaInitialDrainCuQRead.of_event {X : Execution} {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (he : X.get i = some ⟨2653,.rd a bytes⟩) :
    MmaInitialDrainCuQRead X i a bytes := he

theorem mmaInitialDrainAddressesOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (hProtected : ∀ Y, Consistent l kernel Assumptions.all m Y → DrainCuQProtected p Y) :
    MmaInitialDrainAddresses p X := by
  intro i a bytes he
  obtain ⟨g,j⟩ := i
  obtain ⟨Y,hXY,hMax⟩ := maximalExtension hp hX
  exact firstDrainReadOfMaximal hp hMax (hProtected Y hMax.1) (Execution.le_get hXY he)

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
