-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadySite
public import Kernels.TmlFa4Fwd.Proof.LoaderCacheWords
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeySite
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmValueSite
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingKeyPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingValuePrefix
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.LoaderCopySize
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingBiasWarp
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Lemmas.Flow.NotBulk
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

set_option maxRecDepth 100000 in
private theorem ordinaryCopySites :
    (kernel.code.zipIdx).all (fun (ins, pc) =>
      !bulkOp ins.op || (packetCopyOp ins.op &&
        decide (297 < pc ∧ pc < 1862 ∧ pc ∉ registerHintSites))) = true := by
  kernel_rfl

private theorem actualCopyPacket {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}
    (he : X.get i = some ⟨pc, .copy s⟩) :
    (297 < pc ∧ pc < 1862 ∧ pc ∉ registerHintSites) ∧
      ∃ (packet : Fin 6) (pair : Fin 16) (upper : Bool), pc = packetPlanePc packet pair upper := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨t, ins, o, _, hCode, hFire⟩
  · cases hf
  have hMem : (ins, pc) ∈ kernel.code.zipIdx := by
    apply List.mem_of_getElem? (i := pc)
    simp [hCode]
  have hIsCopy := fires_bulk_op hFire rfl
  have hAudit := List.all_eq_true.mp ordinaryCopySites (ins, pc) hMem
  have hFacts : packetCopyOp ins.op = true ∧ 297 < pc ∧ pc < 1862 ∧ pc ∉ registerHintSites := by
    simpa only [hIsCopy, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
      using hAudit
  have hAt : packetCopyAt pc = true := by simpa [packetCopyAt, hCode] using hFacts.1
  obtain ⟨packet, hLo, hHi⟩ := loaderCopyPcInPacket (by have := hFacts.2.1; omega)
    (by have := hFacts.2.2.1; omega) hAt
  obtain ⟨pair, upper, hSite⟩ := packetCopyCoordinates packet hLo hHi hAt
  exact ⟨hFacts.2, packet, pair, upper, hSite⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem ordinaryCopyIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc : Nat} {s : AsyncCopy.Spec} (he : X.get (g, j) = some ⟨pc, .copy s⟩)
    (hPc : 297 < pc ∧ pc < 1862 ∧ pc ∉ registerHintSites) :
    14 ≤ warpIndex l g := by
  have hEarly : 173 < pc := by have := hPc.1; omega
  have hBody := roleBodyPcOfEvent hp hX he hEarly hPc.2.2
  change roleBodyPc (warpIndex l g) pc at hBody
  unfold roleBodyPc at hBody
  have body := hBody.resolve_left (by have := hPc.2.1; omega : pc ≠ 9205)
  by_contra! hWrong
  rw [ite_eq_right (by omega : ¬ 14 ≤ warpIndex l g)] at body
  split at body
  · have := hPc.2.1; omega
  split at body
  · have := hPc.2.1; omega
  split at body <;> have := hPc.2.1 <;> omega

private theorem primingCopyByte (hp : Pre p l m) (hFrame : OutputFootprint p X)
    {batch head row tid k : Nat} (hb : batch < p.batch) (hh : head < p.kvHeads) (value upper : Bool)
    {spec : AsyncCopy.Spec}
    (hSource : spec.src.loc = (if value then p.vLayout else p.kLayout).loc
      (primingScratchPage p batch row) head (row % 16) (kvCopyColumn tid upper)) (hk : k < 16) :
    ((if value then p.vLayout else p.kLayout).region p.pages p.kvHeads).Contains
        (spec.src.loc.at k) ∧
      (∃ byte, m (spec.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (spec.src.loc.at k) := by
  let layout := if value then p.vLayout else p.kLayout
  let page := primingScratchPage p batch row
  let col := kvCopyColumn tid upper
  let inPage := row % 16
  have hPage : page < p.pages := primingScratchPageBound hp hb
  have hRow : inPage < 16 := Nat.mod_lt _ (by decide)
  have hCol := kvCopyColumn_byte_lt (lane := tid) upper hk
  have hLayout : layout.region p.pages p.kvHeads ∈ p.inputRegions := by
    cases value <;> simp [layout, Params.inputRegions]
  rw [hSource]
  have hSpan := CacheLayout.loc_copy_in_region (c := layout) hPage hh hRow hCol
  have hBytes := hp.kvBytes page hPage head hh inPage hRow (col + k / 2) hCol
  have hInit : ∃ byte, m ((layout.loc page head inPage col).at k) = some (some byte) := by
    rw [layout.loc_copy_byte]
    have hBound : k % 2 < 2 := Nat.mod_lt _ (by decide)
    cases value
    · exact ⟨_, hBytes.1 _ (by simp [Value.bytes, FloatFmt.bytes]; omega)⟩
    · exact ⟨_, hBytes.2 _ (by simp [Value.bytes, FloatFmt.bytes]; omega)⟩
  exact ⟨hSpan, hInit, fun _ _ _ hw => hFrame.input_unwritten hp hLayout hSpan hw⟩

set_option maxRecDepth 100000 in
private theorem ordinaryCopyBacking (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy i spec) :
    CacheWords m spec.src ∧
      (∀ k < spec.src.size,
        ((p.kLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∨
         (p.vLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k)) ∧
        (∃ byte, m (spec.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (spec.src.loc.at k)) := by
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, he⟩ := hCopy
  obtain ⟨hPc, packet, pair, upper, hSite⟩ := actualCopyPacket hX he
  have hWarp := ordinaryCopyIssuer hp hX he hPc
  have hCTA := loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he hPc.1 hPc.2.1
  have hShape := actualCopyShape hX (show X.Copy (g, j) spec from ⟨_, he⟩)
  have hSize := hShape.srcSize.trans_eq hShape.widthEq
  rw [hSite] at he
  have key {k : Nat} (h : (p.kLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∧
      (∃ byte, m (spec.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (spec.src.loc.at k)) :=
    And.intro (Or.inl h.1 : (p.kLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∨
      (p.vLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k)) h.2
  have value {k : Nat} (h : (p.vLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∧
      (∃ byte, m (spec.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (spec.src.loc.at k)) :=
    And.intro (Or.inr h.1 : (p.kLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∨
      (p.vLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k)) h.2
  fin_cases packet
  · have same : packetPlanePc 0 pair upper = kCopyPc pair + if upper then 1 else 0 := by
      fin_cases pair <;> cases upper <;> decide
    have h : PrimingKeyVector X (g, j) pair upper spec := by
      change X.get (g, j) = some ⟨packetPlanePc 0 pair upper, .copy spec⟩ at he
      rwa [same] at he
    obtain ⟨batch, hb, _, _, hh, _, hs⟩ := h.source hp hX hFrame hWarp hCTA
    let co := assignedCoordinates p batch (g / l.block)
    let row := kvCopyRow (Mma.trips p batch co.1 - 1) (g % l.block) pair.val
    refine ⟨cacheWordsOfLayout hp (lane := g % l.block) (primingScratchPageBound hp (row := row) hb)
      hh (Nat.mod_lt row (by decide)) false upper hSize hs, ?_⟩
    exact fun k hk => key (primingCopyByte hp hFrame hb hh false upper hs (hk.trans_le hSize))
  · have same : packetPlanePc 1 pair upper = vCopyPc pair + if upper then 1 else 0 := by
      fin_cases pair <;> cases upper <;> decide
    have h : PrimingValueVector X (g, j) pair upper spec := by
      change X.get (g, j) = some ⟨packetPlanePc 1 pair upper, .copy spec⟩ at he
      rwa [same] at he
    obtain ⟨batch, hb, _, _, hh, _, hs⟩ := h.source hp hX hFrame hWarp hCTA
    let co := assignedCoordinates p batch (g / l.block)
    let row := kvCopyRow (Mma.trips p batch co.1 - 1) (g % l.block) pair.val
    refine ⟨cacheWordsOfLayout hp (lane := g % l.block) (primingScratchPageBound hp (row := row) hb)
      hh (Nat.mod_lt row (by decide)) true upper hSize hs, ?_⟩
    exact fun k hk => value (primingCopyByte hp hFrame hb hh true upper hs (hk.trans_le hSize))
  · have h := WarmKeySite.backing hp hX hFrame ⟨pair, upper, he⟩
    exact ⟨h.1, fun k hk => key (h.2 k hk)⟩
  · have h := WarmValueSite.backing hp hX hFrame ⟨pair, upper, he⟩
    exact ⟨h.1, fun k hk => value (h.2 k hk)⟩
  · have h : SteadyKeySite X (g, j) spec := ⟨pair, upper, he⟩
    exact ⟨h.words hp hX hFrame, fun k hk => key (h.backed hp hX hFrame k hk)⟩
  · have h : SteadyValueSite X (g, j) spec := ⟨pair, upper, he⟩
    exact ⟨h.words hp hX hFrame, fun k hk => value (h.backed hp hX hFrame k hk)⟩

/-- Every issued ordinary copy reads live bytes of the launch-provided K or V cache.
The execution prefix may end before the copy is committed. -/
theorem ordinaryCopyBacked (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy i spec) :
    ∀ k < spec.src.size,
      ((p.kLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∨
       (p.vLayout.region p.pages p.kvHeads).Contains (spec.src.loc.at k)) ∧
      (∃ byte, m (spec.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (spec.src.loc.at k) :=
  (ordinaryCopyBacking hp hX hFrame hCopy).2

/-- Every live BF16 pair of an actual loader copy is initialized by one cache element. -/
theorem ordinaryCopyWords (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy i spec)
    : CacheWords m spec.src :=
  (ordinaryCopyBacking hp hX hFrame hCopy).1

/-- The actual masked-copy size always preserves the boundaries of BF16 words. -/
theorem ordinaryCopySize (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {spec : AsyncCopy.Spec} (hCopy : X.Copy i spec) :
    spec.src.size = 0 ∨ spec.src.size = 16 := by
  obtain ⟨g,j⟩ := i
  obtain ⟨pc,he⟩ := hCopy
  obtain ⟨hPc,_,_,_,_⟩ := actualCopyPacket hX he
  have hWarp := ordinaryCopyIssuer hp hX he hPc
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hEq : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  obtain ⟨start,_,hIndex,hStart,hRun⟩ := nonzeroCommonPrefixOfLateEvent hp hX
    (event_thread_lt hX he) (by omega : 0 < warpIndex l g) he (show 173 < pc by omega)
  obtain ⟨vs,hWalk⟩ := Mma.walkFromRun hRun
  have hNext : ((X.tr g).drop 5)[j - 5]? = some ⟨pc,.copy spec⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hFrame : Holds start.regs [(2535,b32 l.sharedBase),(1062,b32 (14 + warp.val))] :=
    ⟨hStart.2.2.2.2.2.1,hEq.symm ▸ hStart.2.2.2.2.1,trivial⟩
  have hSeen := loaderEventInClosedSlice (stop := 1901) warp (by decide) le_rfl
    (by intro; rfl) hWalk (by rw [hStart.1]; decide)
    (ringShapeOfAt hStart) hFrame (List.mem_of_getElem? hNext)
    (show pc < 1901 from hPc.2.1.trans (by decide))
  exact loaderCopyReadSize hWalk hStart.1 hSeen rfl

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
