-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainRoot
import all Kernels.TmlFa4Fwd.Proof.LoaderSelectedCoordinates
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduler
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Flow.Code.Part142

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.RowDrainRole
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

def batchReg : RowDrainRole → Nat
  | .softmax => 7151
  | .correction => 7153

def guardReg : RowDrainRole → Nat
  | .softmax => 652
  | .correction => 744

def guardSite : RowDrainRole → Nat
  | .softmax => 7618
  | .correction => 9086

def addressReg : RowDrainRole → Nat
  | .softmax => 8982
  | .correction => 9531

def loadDst : RowDrainRole → Nat
  | .softmax => 7259
  | .correction => 7279

def roots (role : RowDrainRole) (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (role.batchReg,b32 p.batch) :: role.frame p l g

def guarded (role : RowDrainRole) (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (role.guardReg,.pred (decide (p.batch < laneOf l g))) :: role.roots p l g

theorem signedWord {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned,toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega),ite_eq_left hn]

private def coreInstruction (pair : Instr × Nat) : Bool :=
  Assumptions.coreOp pair.1.op && !Assumptions.swExp2Sites.contains pair.2 &&
    !Assumptions.tcLdDataflowSites.contains pair.2 && !Assumptions.delayedTmemSites.contains pair.2

theorem drainCore (role : RowDrainRole) {l : Launch} {g : Nat} {s : TState}
    (hLo : role.start ≤ s.pc) (hHi : s.pc < role.exitFloor) :
    out kernel Assumptions.all l g s = out kernel [] l g s := by
  cases hf : s.fault
  · cases hc : kernel.code[s.pc]? with
    | none => simp only [out,hf,hc]
    | some ins =>
      let code := ((kernel.code.drop role.start).take (role.exitFloor-role.start)).zipIdx
        role.start
      have hAudit : code.all coreInstruction = true := by cases role <;> decide +kernel
      have hCode : coreInstruction (ins,s.pc) = true := by
        apply List.all_eq_true.mp hAudit
        apply List.mem_of_getElem? (i := s.pc-role.start)
        dsimp [code]
        rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
          Nat.add_sub_of_le hLo,hc]
        rfl
      simp only [coreInstruction, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hCode
      exact Assumptions.out_all_eq_nil hCode.1.1.2 hCode.1.2 hCode.2 hc hCode.1.1.1
  · simp only [out,hf]

theorem drainLocals (role : RowDrainRole) {l : Launch} {g lo n : Nat}
    {s t : TState} (hLo : role.start ≤ lo) (hHi : lo+n ≤ role.exitFloor) (hPc : s.pc = lo)
    (hStraight : ((kernel.code.drop lo).take (n-1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n s = some t) :
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t :=
  run_rtg (schedulerLocalTransport hStraight (fun _ _ => role.drainCore (by omega) (by omega))
    hr (by omega) (by omega))

private theorem batchParameter (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s : TState} (hs : At s role.start (role.frame p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (role.start+1) (role.roots p l g) := by
  obtain ⟨hWord,hParam⟩ := hp.values (19,p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  have code : kernel.code[role.start]? = some ⟨none, .mem
      {kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param (param 19) false, 0⟩, dsts := [some role.batchReg]}⟩ := by
    cases role
    · rw [Loader.loaderParam19Name]
      exact Flow.code_7605
    · rw [Loader.loaderParam19Name]
      exact Flow.code_9083
  have hr : run kernel [] l g 1 s = some (next (setReg s role.batchReg (b32 p.batch))) :=
    Loader.scalarLoad hs hParam hWord code
  exact ⟨_,role.drainLocals le_rfl (by cases role <;> decide) hs.1 (by simp) hr,
    hs.set (by cases role <;> simp [frame,batchReg,laneReg,ctaReg])⟩

private theorem initialCompare (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s : TState} (hs : At s (role.start+1) (role.roots p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (role.start+2) (role.guarded p l g) := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.1
  have hL32 : laneOf l g < 2^32 := by omega
  have hL31 : laneOf l g < 2^31 := by omega
  have hB32 : p.batch < 2^32 := by omega
  have hB31 := hBatch
  have hLocal : ∃ u, run kernel [] l g 1 s = some u ∧
      At u (role.start+2) (role.guarded p l g) := by
    cases role <;> dsimp only [start,guarded,guardReg,roots,batchReg,frame,laneReg,ctaReg] at hs ⊢
    all_goals seg_fp hs using simp only [truncBits_ofNat hL32 (by decide),
      truncBits_ofNat hB32 (by decide), compare, Option.getD_some, signedWord hL31,
      signedWord hB31, gt_iff_lt, Int.ofNat_lt]
  obtain ⟨u,hr,hu⟩ := hLocal
  exact ⟨u,role.drainLocals (Nat.le_succ _) (by cases role <;> decide) hs.1 (by simp) hr,hu⟩

/-- Replay the actual first drain to the optional lookup guard. -/
theorem firstGate (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos j pc : Nat} {s : TState} {ending : Option TState}
    {a : Acc} {bytes : List (Option Byte)}
    (hs : At s role.start (role.frame p l g))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hPos : pos ≤ j) (he : X.get (g,j) = some ⟨pc,.rd a bytes⟩)
    (hSite : pc = role.firstRead ∨ pc = role.laterRead) :
    ∃ nextPos ≤ j, ∃ u, At u role.guardSite (role.guarded p l g) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop nextPos) ending := by
  obtain ⟨t,hBatch,ht⟩ := role.batchParameter hp (g := g) hs
  obtain ⟨v,hCompare,hv⟩ := role.initialCompare hp (g := g) ht
  have hRun := hr.after_local_nonempty (hBatch.trans hCompare)
    (Loader.traceAfterObservedEvent he hPos)
  let span : RowDrainSpan := ⟨role.start+2,role.guardSite,role.exitFloor⟩
  have hCode : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected ((role.guarded p l g).map Prod.fst) i.op) = true := by
    simp only [guarded,roots,frame,List.map_cons,List.map_nil]
    cases role <;> decide +kernel
  have hSegments : span.segmentKeeps ((role.guarded p l g).map Prod.fst) := by
    apply span.segmentKeeps_of_audit
    simp only [guarded,roots,frame,List.map_cons,List.map_nil]
    cases role <;> decide +kernel
  have hAbove {s t : TState} {es : List Event}
      (hPath : TraceReach kernel Assumptions.all l g s es t) (hLo : span.bypass ≤ s.pc) :
      span.bypass ≤ t.pc :=
    span.traceAboveExit hPath (by cases role <;> decide +kernel) (by cases role <;> decide) hLo
  have hBand : span.stop ≤ pc ∧ pc < span.bypass := by
    rcases hSite with rfl | rfl <;> cases role <;> decide
  have hSpan : ∃ ins, kernel.code[span.stop]? = some ins ∧ ins.op.isLocal = true := by
    cases role
    · exact ⟨_,Flow.code_7618,rfl⟩
    · exact ⟨_,Flow.code_9086,rfl⟩
  obtain ⟨_,hStop,hLocal⟩ := hSpan
  exact span.replayTo hp (by cases role <;> decide) hCode hSegments hAbove hStop hLocal hv hRun
    hPos he (by intro f h; cases h) ⟨fun h => Nat.not_lt_of_ge hBand.1 h.2,hBand.2⟩

theorem firstBranch (role : RowDrainRole) {p : Params} {l : Launch}
    {g : Nat} {s : TState} (hs : At s role.guardSite (role.guarded p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if p.batch < laneOf l g then role.firstRead+1 else role.firstRead-2)
        (role.roots p l g) := by
  have hGuard := hs.2.2.2.2.1
  cases role
  · obtain ⟨u,hr,hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g) Flow.code_7618
      _ hs hGuard (by simp)
    exact ⟨u,RowDrainRole.softmax.drainLocals (by decide) (by decide) hs.1 (by simp) hr,
      by simpa only [decide_eq_true_eq,firstRead] using hu.mono hu.2.2.2.2.2⟩
  · obtain ⟨u,hr,hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g) Flow.code_9086
      _ hs hGuard (by simp)
    exact ⟨u,RowDrainRole.correction.drainLocals (by decide) (by decide) hs.1 (by simp) hr,
      by simpa only [decide_eq_true_eq,firstRead] using hu.mono hu.2.2.2.2.2⟩


theorem firstTemplate (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s : TState} (hi : laneOf l g ≤ p.batch)
    (hs : At s (role.firstRead-2) (role.roots p l g)) :
    let a : Acc := {loc := globalLoc (p.cuQBase + 4*laneOf l g), size := 4}
    ∃ t, At t role.firstRead
        ((role.addressReg,b64 (p.cuQBase + 4*laneOf l g)) :: role.roots p l g) ∧
      Next kernel Assumptions.all l g s t (.read a (afterLoad t [role.loadDst])) := by
  dsimp only
  have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch+1) ≤ 2^64 at hRange
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hL32 : laneOf l g < 2^32 := by omega
  have hL64 : laneOf l g < 2^64 := by omega
  have hOff : 4 * laneOf l g < 2^64 := by omega
  have hBase : p.cuQBase < 2^64 := by omega
  have hAddr : p.cuQBase+4*laneOf l g < 2^64 := by omega
  have h4 : (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 := rfl
  have hLocal : ∃ t, run kernel [] l g 2 s = some t ∧
      At t role.firstRead
        ((role.addressReg,b64 (p.cuQBase+4*laneOf l g)) :: role.roots p l g) := by
    cases role <;> dsimp only [firstRead,addressReg,roots,batchReg,frame,laneReg,ctaReg] at hs ⊢
    all_goals seg_fp hs using simp only [b64,kind_u_beq_s,Bool.false_eq_true,↓reduceIte,
      truncBits_ofNat hL32 (by decide),toNat_ofNat_lt hL64,h4,Nat.mul_comm (laneOf l g),
      truncBits_ofNat hOff (by decide),truncBits_ofNat hBase (by decide),
      ← BitVec.ofNat_add,truncBits_ofNat hAddr (by decide)]
  obtain ⟨t,hr,ht⟩ := hLocal
  have hPath := role.drainLocals (lo := role.firstRead-2) (n := 2)
    (by cases role <;> decide) (by cases role <;> decide) hs.1 (by cases role <;> decide +kernel) hr
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  have hAligned : (p.cuQBase + 4*laneOf l g) % 4 = 0 := by omega
  have hCore := role.drainCore (l := l) (s := t) (g := g)
    (by rw [ht.1]; cases role <;> decide) (by rw [ht.1]; cases role <;> decide)
  refine ⟨t,ht,⟨hPath,?_⟩⟩
  rw [hCore]
  cases role
  · rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_7621) rfl rfl]
    exact congrArg Out.ev (loadTmpl_global ht.2.1 ht.2.2.2.2.1 hAddr (by decide) hAligned)
  · rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_9089) rfl rfl]
    exact congrArg Out.ev (loadTmpl_global ht.2.1 ht.2.2.2.2.1 hAddr (by decide) hAligned)

private theorem firstReadFloor (role : RowDrainRole) {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {ending : Option TState} (hs : role.firstRead < s.pc)
    (hr : Run kernel Assumptions.all l g s events ending) :
    ∀ e ∈ events, role.firstRead < e.pc := by
  have hCode : (kernel.code.drop (role.firstRead+1)).all
      (fun i => staysPastEvent (role.firstRead+1) i.op) = true := by
    cases role <;> decide +kernel
  have hSites : ∀ pc ∈ Assumptions.swExp2Sites, pc < role.firstRead+1 := by
    cases role <;> decide
  obtain ⟨_,hw⟩ := Mma.walkFromRun hr
  exact eventTailEventsOfSegmentFloor hCode
    (fun pc hLo hm _ _ => (Nat.not_lt_of_ge hLo (hSites pc hm)).elim) hw hs

/-- A first drain lookup is the requesting lane's launch metadata word. -/
@[no_expose] def FirstCuQRead (role : RowDrainRole) (X : Execution) (i : EvId)
    (a : Acc) (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨role.firstRead,.rd a bytes⟩

theorem FirstCuQRead.word {role : RowDrainRole} {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (he : FirstCuQRead role X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index), size := 4} := by
  obtain ⟨g,j⟩ := i
  have hGet : X.get (g,j) = some ⟨role.firstRead,.rd a bytes⟩ := he
  obtain ⟨pos,hPos,s,ending,hs,hr⟩ := role.checkpointOfRead hp hX hCuQ (.inl rfl) hGet
  obtain ⟨pos',hPos',t,ht,hTail⟩ := role.firstGate hp hs hr hPos hGet (.inl rfl)
  obtain ⟨u,hu,hU⟩ := role.firstBranch ht
  by_cases hi : laneOf l g ≤ p.batch
  · have hAt : At u (role.firstRead-2) (role.roots p l g) := by
      simpa only [ite_eq_right (Nat.not_lt_of_ge hi)] using hU
    obtain ⟨v,hV,hNext⟩ := role.firstTemplate hp hi hAt
    exact ⟨_,hi,(hNext.uniqueScalarReadAt hV.1
      (hTail.after_local_nonempty hu (Loader.traceAfterObservedEvent hGet hPos')) hPos' hGet
      (fun _ _ hPc hRest => role.firstReadFloor hPc hRest)).2⟩
  · have hAt : role.firstRead < u.pc := by
      rw [hU.1,ite_eq_left (Nat.lt_of_not_ge hi)]
      omega
    have hMem : (⟨role.firstRead,.rd a bytes⟩ : Event) ∈ (X.tr g).drop pos' := by
      apply List.mem_of_getElem? (i := j-pos')
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos']
      exact hGet
    have hr' := hTail.after_local_nonempty hu (Loader.traceAfterObservedEvent hGet hPos')
    exact (Nat.lt_irrefl _ (role.firstReadFloor hAt hr' _ hMem)).elim

end PTX.Kernels.TmlFa4Fwd.Thread.RowDrainRole
