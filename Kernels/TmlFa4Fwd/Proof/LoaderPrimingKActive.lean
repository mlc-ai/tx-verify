-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKTripEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSecondSlot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue

noncomputable section

private def boundedLocalFrameOp (lower upper : Nat) (regs : List Nat) (op : Op) : Bool :=
  regs.all (fun reg => !(loaderRingWrites op).contains reg) &&
    match op with
    | .bra target _ => lower ≤ target && target ≤ upper
    | .brx .. => false
    | _ => true

private theorem boundedLocalTargets {lower upper pc : Nat} {op : Op}
    (h : (match op with
      | .bra target _ => lower ≤ target && target ≤ upper
      | .brx .. => false
      | _ => true) = true) :
    (∀ target, ¬ BrxTarget op target) ∧
      (nextPc op pc = pc + 1 ∨ lower ≤ nextPc op pc ∧ nextPc op pc ≤ upper) := by
  cases op <;> simp only [Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  case bra target uni => exact ⟨by simp [BrxTarget], .inr h⟩
  all_goals exact ⟨by simp [BrxTarget], .inl rfl⟩

/-- Step-count slack makes a decoded branch window usable for local frame preservation
even though an internal backedge keeps the current PC from increasing on every step. -/
private theorem boundedLocalFrame {l : Launch} {g lower upper stop n : Nat}
    {s u : TState} {F : List (Nat × Value)} (hLower : 174 ≤ lower) (hStop : stop ≤ 1901)
    (hCode : ((kernel.code.drop lower).take (stop - lower)).all
      (fun ins => boundedLocalFrameOp lower upper (F.map Prod.fst) ins.op) = true)
    (hs : lower ≤ s.pc) (hPC : s.pc + n ≤ stop) (hBudget : upper + n ≤ stop)
    (hF : Holds s.regs F) (hRun : run kernel Assumptions.all l g n s = some u) :
    Holds u.regs F := by
  induction n generalizing s with
  | zero => exact (Option.some.inj hRun) ▸ hF
  | succ n ih =>
    rw [run] at hRun
    cases hNext : tauStep kernel Assumptions.all l g s with
    | none => simp [hNext] at hRun
    | some z =>
      rw [hNext, Option.bind_some] at hRun
      have hTau := tauStep_iff.mp hNext
      have hTauCore : Tau kernel [] l g s z := by
        unfold Tau at hTau ⊢
        rwa [← loaderOutCore (by omega) (by omega)]
      obtain ⟨ins, hc⟩ := tau_core_has_code hTauCore
      have hLookup : ((kernel.code.drop lower).take (stop - lower))[s.pc - lower]? = some ins := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hs]
        exact hc
      obtain ⟨hKeep, hTarget⟩ := Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp hCode _ (List.mem_of_getElem? hLookup))
      have hFrame (reg : Nat) (hReg : reg ∈ F.map Prod.fst) : z.regs reg = s.regs reg := by
        apply loaderPipelineStepRegs (by omega) (by omega) _ (.inl ⟨rfl, hTau⟩)
        intro other hOther
        cases Option.some.inj (hc.symm.trans hOther)
        simpa using List.all_eq_true.mp hKeep reg hReg
      have hRegs := holdsSchedulerFrame hF hFrame (fun _ hm => List.mem_map_of_mem hm)
      obtain ⟨hNo, hNextPc⟩ := boundedLocalTargets (pc := s.pc) hTarget
      have hz : z.pc = s.pc + 1 ∨ lower ≤ z.pc ∧ z.pc ≤ upper := by
        rcases tau_core_frame hc hTauCore with rfl | h
        · exact .inl rfl
        · rw [h.pc.resolve_right (hNo _)]
          exact hNextPc
      exact ih (by rcases hz with h | h <;> omega) (by rcases hz with h | h <;> omega)
        (by omega) hRegs hRun

/-- Values preserved across the active request's page-size arithmetic. -/
def primingKShiftCarry (p : Params) (l : Launch) (batch head warp lane : Nat) :
    List (Nat × Value) :=
  let tid := 32 * warp + lane
  [(7169, b32 head), (7505, b64 p.pageTableStride), (7297, b64 batch),
   (7504, b64 p.pageTableBase), (1086, b32 (p.kLength batch)),
   (1085, b32 (2 ^ 32 - p.qLength batch)),
   (7294, b64 (l.localBase + 64)), (7295, b64 (l.localBase + 96)), (2535, b32 l.sharedBase),
   (1081, b32 (tid / 8 % 8)), (1082, b32 (kvCopyColumn tid false)),
   (1062, b32 (tid / 32)), (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
   (7495, b64 p.kLayout.pageStride), (7493, b64 p.kLayout.rowStride),
   (7292, b64 l.localBase), (7497, b64 p.vLayout.rowStride),
   (7499, b64 p.vLayout.pageStride)] ++ addressCacheInputs p

def primingKActiveFacts (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    List (Nat × Value) :=
  [(7168, b32 tile), (1799, b32 (p.qOffset batch)), (103, .pred false),
   (7296, b64 16), (1798, b32 16)] ++ primingKShiftCarry p l batch head warp lane

/-- The actual active request's shift and zero reciprocal select the 16-row page formula. -/
theorem primingKActiveToAddressLaneWithExtra {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch head tile warp lane : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    {s : TState} {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop 386).take (451 - 386)).all
      (fun ins => (F.map Prod.fst).all (fun r => !(loaderRingWrites ins.op).contains r)) = true)
    (hs : At s 386 (primingKActiveFacts p l batch head tile warp lane ++ F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
        At u 415 (primingKAddressFacts p l batch head tile warp lane ++ F) := by
  have hPacked : p.qOffset batch + 256 * tile < 2 ^ 32 := by
    have := hp.packedRow_lt hb hTile
    have := hp.shape.2.2.2.2.2
    omega
  have ⟨hCore, hExtra⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨v, hv, hV⟩ := loaderQueryShiftLoop (l := l) (g := g) hPacked
    s (hs.mono ((holds_append ..).mp hCore).1)
  obtain ⟨u, hu, hU⟩ := loaderShiftReciprocal v hV
  have hRun := run_comp hv hu
  have hF := boundedLocalFrame (F := primingKShiftCarry p l batch head warp lane) (lower := 386)
    (upper := 415) (stop := 451) (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by rw [hs.1]) (by rw [hs.1]; decide) (by decide) ((holds_append ..).mp hCore).2 hRun
  have hBranch : ((kernel.code.drop 386).take (451 - 386)).all
      (fun ins => boundedLocalFrameOp 386 415 [] ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCode : ((kernel.code.drop 386).take (451 - 386)).all
      (fun ins => boundedLocalFrameOp 386 415 (F.map Prod.fst) ins.op) = true := by
    apply List.all_eq_true.mpr
    intro ins hm
    simp only [boundedLocalFrameOp, Bool.and_eq_true]
    refine ⟨List.all_eq_true.mp hKeep ins hm, ?_⟩
    simpa only [boundedLocalFrameOp, List.all_nil, Bool.true_and] using
      List.all_eq_true.mp hBranch ins hm
  refine ⟨u, run_rtg hRun, hU.mono ?_⟩
  apply (holds_append ..).mpr
  refine ⟨?_, boundedLocalFrame (lower := 386) (upper := 415) (stop := 451)
    (by decide) (by decide) hCode (by rw [hs.1]) (by rw [hs.1]; decide)
    (by decide) hExtra hRun⟩
  simp only [primingKAddressFacts, addressPreludeInputs, addressCacheInputs,
    primingKAddressCarry, List.cons_append, List.nil_append, Holds]
  repeat' apply And.intro
  all_goals first
    | trivial
    | apply holds_lookup hU.2.2.2.2; rfl
    | apply holds_lookup hF; rfl

/-- The actual active request's shift and zero reciprocal select the 16-row page formula. -/
theorem primingKActiveToAddressLane {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch head tile warp lane : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    {s : TState} (hs : At s 386 (primingKActiveFacts p l batch head tile warp lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
        At u 415 (primingKAddressFacts p l batch head tile warp lane) :=
  primingKActiveToAddressLaneWithExtra hp hb hTile (F := [])
    (by set_option maxRecDepth 100000 in kernel_rfl) (by simp only [List.append_nil]; exact hs)

/-- The local segment applied to every lane of a continuing warp. -/
theorem primingKActiveToAddress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch head tile warp shuffles votes : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    (cur : SchedulerWarpAt l X g 386 (primingKActiveFacts p l batch head tile warp)
      shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 415 (primingKAddressFacts p l batch head tile warp)
      shuffles votes) := by
  apply cur.advanceLocal
  intro lane hl
  exact primingKActiveToAddressLane hp hb hTile (cur.checkpoint lane hl)

/-- Loader ABI words carried by the selected-request scheduler. -/
def primingKActiveAbi (p : Params) (l : Launch) (warp : Nat) : List (Nat × Value) :=
  [(1062, b32 warp), (2535, b32 l.sharedBase),
   (7292, b64 l.localBase), (7294, b64 (l.localBase + 64)), (7295, b64 (l.localBase + 96)),
   (7504, b64 p.pageTableBase), (7505, b64 p.pageTableStride),
   (7493, b64 p.kLayout.rowStride), (7495, b64 p.kLayout.pageStride),
   (7497, b64 p.vLayout.rowStride), (7499, b64 p.vLayout.pageStride)] ++ addressCacheInputs p

private theorem loaderPrimingTid {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g lane : Nat} (hg : g < l.threads) (hl : lane < 32) :
    warpLane l g lane % l.block = 32 * Prologue.warpIndex l g + lane := by
  obtain ⟨hSame, hLane⟩ := Step.sameWarp_lane (L := l) (by rw [hp.block]) hg hl
  have hWarp := hSame.2
  change g % l.block / 32 = warpLane l g lane % l.block / 32 at hWarp
  change warpLane l g lane % l.block % 32 = lane at hLane
  unfold Prologue.warpIndex
  omega

/-- Lane and page-scale words needed by the recurring loader. -/
def warmLaneRoots (l : Launch) (tid : Nat) : List (Nat × Value) :=
  [(1061, b32 tid), (1663, b32 16), (7293, b64 (l.localBase + 32))]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g first batch shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ending : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 311
      (loaderCoordinateFacts p l g (Prologue.warpIndex l g) first batch) shuffles votes ending)
include hp hb hLo hHi cur

/-- The selected CTA coordinates and startup ABI reach the actual metadata reads. -/
theorem primingKActiveEntryWithLaneRootsPreserving :
    ∃ next : SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ (primingKActiveAbi p l (Prologue.warpIndex l g) ++
        warmLaneRoots l (warpLane l g lane % l.block)))
      shuffles votes ending,
      next.pos = cur.pos ∧ next.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let tid := thread % l.block
  let pos := assignedCoordinates p batch (g / l.block)
  let extra := primingKActiveAbi p l (Prologue.warpIndex l g) ++ warmLaneRoots l tid
  let carry := [(1663, b32 16), (1061, b32 tid), (2535, b32 l.sharedBase),
    (7502, b64 p.cuQBase), (7503, b64 p.usedKBase)] ++ extra
  have ht := cur.checkpoint lane hl
  have hArgs : At (cur.state lane) 311
      [(1754, b32 (requestTiles p batch)), (7136, b32 p.heads),
       (1756, b32 (g / l.block - tilePrefix p batch * p.heads)), (7154, b32 800),
       (7144, b32 p.batch), (7170, b32 batch)] := by at_select ht
  have hCarry : Holds (cur.state lane).regs carry := by
    simp only [carry, extra, warmLaneRoots, primingKActiveAbi, addressCacheInputs, List.cons_append,
      List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | exact holds_lookup ht.2.2.2.2 rfl
  obtain ⟨v, hv, hV⟩ := loaderTileHead hp thread hb hLo hHi (cur.state lane) hArgs
  obtain ⟨hvA, hVFrame⟩ := loaderLinear (regs := carry.map Prod.fst)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hf := holdsSchedulerFrame hCarry hVFrame (fun _ hm => List.mem_map_of_mem hm)
  have hVEntry : At v 354 (activeEntryInputs p l tid batch pos.1 pos.2 ++ extra) := by
    apply hV.mono
    refine (holds_append ..).mpr ⟨?_, hf.2.2.2.2.2⟩
    simp only [activeEntryInputs, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | apply holds_lookup hV.2.2.2.2; rfl
      | apply holds_lookup hf; rfl
  have hTid : tid < 512 := by rw [← hp.block]; exact Nat.mod_lt _ (by rw [hp.block]; decide)
  obtain ⟨u, hu, hU⟩ := loaderActiveEntryFrame hp hTid hb
    (by set_option maxRecDepth 100000 in kernel_rfl) hVEntry
  exact ⟨u, run_rtg (run_comp hvA hu), hU⟩

/-- The active coordinate replay preserves the actual lane indices. -/
theorem primingKActiveEntryFromCoordinatesWithLaneRootsAt :
    ∃ next : SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ (primingKActiveAbi p l (Prologue.warpIndex l g) ++
        warmLaneRoots l (warpLane l g lane % l.block)))
      shuffles votes ending,
      next.pos = cur.pos := by
  obtain ⟨result,hPos,_⟩ := primingKActiveEntryWithLaneRootsPreserving hp hb hLo hHi cur
  exact ⟨result,hPos⟩

/-- The selected CTA coordinates and startup ABI reach the actual metadata reads. -/
theorem primingKActiveEntryFromCoordinatesAt :
    ∃ next : SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ primingKActiveAbi p l (Prologue.warpIndex l g))
      shuffles votes ending,
      next.pos = cur.pos := by
  obtain ⟨next, hPosition⟩ := primingKActiveEntryFromCoordinatesWithLaneRootsAt hp hb hLo hHi cur
  obtain ⟨out, hOut⟩ := next.advanceLocalAt (pc' := 381) (fun lane hl =>
    let hAt := next.checkpoint lane hl
    ⟨_, .refl, hAt.mono (by
      rw [← List.append_assoc] at hAt
      exact ((holds_append ..).mp hAt.2.2.2.2).1)⟩)
  exact ⟨out, hOut.trans hPosition⟩
end

/-- The active entry in a terminated trace. -/
theorem primingKActiveEntryFromCoordinates {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first batch shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (cur : SchedulerWarpAt l X g 311
      (loaderCoordinateFacts p l g (Prologue.warpIndex l g) first batch) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ primingKActiveAbi p l (Prologue.warpIndex l g))
      shuffles votes) := by
  obtain ⟨next, _⟩ := primingKActiveEntryFromCoordinatesAt hp hb hLo hHi cur
  exact ⟨next⟩

/-- Project the first active metadata operands into the priming address replay frame. -/
theorem primingKActiveMetadataFrame {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch lane : Nat} (hg : g < l.threads) (hl : lane < 32)
    (hTile : 256 * (assignedCoordinates p batch (g/l.block)).1 < p.qLength batch)
    {u : TState} {extra : List (Nat × Value)}
    (hU : At u 386 ([(1086,b32 (p.kLength batch)),(1799,b32 (p.qOffset batch)),
      (1800,b32 (p.qOffset (batch+1))),(1085,b32 ((2^32-p.qLength batch)%2^32))] ++
      (loaderActiveLaneFacts p l g batch lane ++
        (primingKActiveAbi p l (Prologue.warpIndex l g) ++ extra)))) :
    let pos := assignedCoordinates p batch (g/l.block)
    At u 386 (primingKActiveFacts p l batch pos.2 pos.1 (Prologue.warpIndex l g) lane ++
      ((7170,b32 batch) :: extra)) := by
  dsimp only
  let warp := Prologue.warpIndex l g
  apply hU.mono
  have hTid := loaderPrimingTid hp hg hl
  have hWarp : (32 * warp + lane) / 32 = warp := by omega
  have hNeg : (2 ^ 32 - p.qLength batch) % 2 ^ 32 = 2 ^ 32 - p.qLength batch := by
    apply Nat.mod_eq_of_lt
    omega
  have hReg : u.regs 1085 = some (b32 (2 ^ 32 - p.qLength batch)) := by
    rw [← hNeg]
    exact holds_lookup hU.2.2.2.2 rfl
  apply (holds_append ..).mpr
  refine ⟨?_, holds_lookup hU.2.2.2.2 rfl, ?_⟩
  · simp only [primingKActiveFacts, primingKShiftCarry, addressCacheInputs,
      List.cons_append, List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | exact holds_lookup hU.2.2.2.2 rfl
      | rw [hWarp]; exact holds_lookup hU.2.2.2.2 rfl
      | rw [← hTid]; exact holds_lookup hU.2.2.2.2 rfl
  · have held := ((holds_append ..).mp hU.2.2.2.2).2
    exact ((holds_append ..).mp ((holds_append ..).mp held).2).2

/-- One lane with a later observed event reads the selected launch metadata. -/
theorem primingKActiveLaneMetadataWithExtra {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles votes lane : Nat} (hg : g < l.threads) (hb : batch < p.batch) (hl : lane < 32)
    (hTile : 256 * (assignedCoordinates p batch (g / l.block)).1 < p.qLength batch)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    {ends : Nat → Option TState} {extra : Nat → List (Nat × Value)}
    (hExtra : ActiveReadExtra (primingKActiveAbi p l (Prologue.warpIndex l g) ++ extra lane))
    (cur : SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ (primingKActiveAbi p l (Prologue.warpIndex l g) ++
        extra lane))
      shuffles votes ends)
    (hProgress : ends lane = none ∨ ∃ (j : Nat) (e : Event), cur.pos lane ≤ j ∧ 385 < e.pc ∧
      X.get (warpLane l g lane, j) = some e) :
    let pos := assignedCoordinates p batch (g / l.block)
    ∃ u, (X.tr (warpLane l g lane)).drop (cur.pos lane) =
      activeMetadataEvents p batch ++ (X.tr (warpLane l g lane)).drop (cur.pos lane + 3) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop (cur.pos lane + 3)) (ends lane) ∧
      At u 386 (primingKActiveFacts p l batch pos.2 pos.1 (Prologue.warpIndex l g) lane ++
        ((7170, b32 batch) :: extra lane)) := by
  let warp := Prologue.warpIndex l g
  let pos := assignedCoordinates p batch (g / l.block)
  have hMore : (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ [] := by
    intro h
    rcases hProgress with hDone | ⟨j, e, hBefore, _, he⟩
    · have hr := cur.continuation lane hl
      rw [h, hDone] at hr
      cases hr
    · exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
        ((List.drop_eq_nil_iff.mp h).trans hBefore)
  obtain ⟨u, h0, h1, h2, hU, hRest⟩ := loaderActiveReadWordsFrameInPrefix hp hX writes hb hExtra
    (cur.checkpoint lane hl)
    ((cur.continuation lane hl).after_local_nonempty (cur.localSteps lane hl) hMore)
    (PrefixDemand.weaken hProgress (by decide))
  refine ⟨u, ?_, hRest, hU.mono ?_⟩
  · have hx := List.getElem?_eq_some_iff.mp h0
    have hy := List.getElem?_eq_some_iff.mp h1
    have hz := List.getElem?_eq_some_iff.mp h2
    rw [List.drop_eq_getElem_cons hx.1, hx.2, List.drop_eq_getElem_cons hy.1, hy.2,
      List.drop_eq_getElem_cons hz.1, hz.2]
    rfl
  · exact (primingKActiveMetadataFrame hp hg hl hTile hU).2.2.2.2

/-- One lane with a later observed event reads the selected launch metadata. -/
theorem primingKActiveLaneMetadata {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles votes lane : Nat} (hg : g < l.threads) (hb : batch < p.batch) (hl : lane < 32)
    (hTile : 256 * (assignedCoordinates p batch (g / l.block)).1 < p.qLength batch)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ primingKActiveAbi p l (Prologue.warpIndex l g))
      shuffles votes ends)
    (hProgress : ends lane = none ∨ ∃ (j : Nat) (e : Event), cur.pos lane ≤ j ∧ 385 < e.pc ∧
      X.get (warpLane l g lane, j) = some e) :
    let pos := assignedCoordinates p batch (g / l.block)
    ∃ u, (X.tr (warpLane l g lane)).drop (cur.pos lane) =
      activeMetadataEvents p batch ++ (X.tr (warpLane l g lane)).drop (cur.pos lane + 3) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop (cur.pos lane + 3)) (ends lane) ∧
      At u 386 (primingKActiveFacts p l batch pos.2 pos.1 (Prologue.warpIndex l g) lane) := by
  have hExtra : ActiveReadExtra (primingKActiveAbi p l (Prologue.warpIndex l g) ++ []) := by
    constructor
    · simp [primingKActiveAbi, addressCacheInputs]
    · simp [primingKActiveAbi, addressCacheInputs]
    · simp [primingKActiveAbi, addressCacheInputs]
    · set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t, hTrace, hRun, ht⟩ :=
    primingKActiveLaneMetadataWithExtra hp hX hg hb hl hTile writes (extra := fun _ => [])
      hExtra (by simpa only [List.append_nil] using cur) hProgress
  exact ⟨t, hTrace, hRun, ht.mono ((holds_append ..).mp ht.2.2.2.2).1⟩

/-- The actual active metadata words seed the exact row, cache and page-table
frame consumed by the first K packet. -/
theorem primingKActiveMetadataFromTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles votes : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hTile : 256 * (assignedCoordinates p batch (g / l.block)).1 < p.qLength batch)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (cur : SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ primingKActiveAbi p l (Prologue.warpIndex l g))
      shuffles votes) :
    let pos := assignedCoordinates p batch (g / l.block)
    Nonempty (SchedulerWarpAt l X g 386
      (primingKActiveFacts p l batch pos.2 pos.1 (Prologue.warpIndex l g)) shuffles votes) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let pos := assignedCoordinates p batch (g / l.block)
  have hLane (lane : Nat) (hl : lane < 32) :
      ∃ u, (X.tr (warpLane l g lane)).drop (cur.pos lane) =
        activeMetadataEvents p batch ++ (X.tr (warpLane l g lane)).drop (cur.pos lane + 3) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop (cur.pos lane + 3)) none ∧
      At u 386 (primingKActiveFacts p l batch pos.2 pos.1 (Prologue.warpIndex l g) lane) :=
    primingKActiveLaneMetadata hp hX hg hb hl hTile writes cur (.inl rfl)
  choose! u hTrace hRun hAt using hLane
  have hCounts := cur.ordinals.advance (fun _ => activeMetadataEvents p batch)
    (fun lane hl => ⟨_, hTrace lane hl⟩) (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨fun lane => cur.pos lane + 3, u, u, hCounts, hRun, fun _ _ => .refl, hAt⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X) {g : Nat}
    (hg : g < l.threads) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (hActive : g / l.block < tilePrefix p p.batch * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hX hComplete hg hWarp hActive writes

end
end PTX.Kernels.TmlFa4Fwd.Loader
