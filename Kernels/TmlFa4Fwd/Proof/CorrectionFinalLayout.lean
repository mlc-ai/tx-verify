-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeSurface
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStats
public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRendezvous
import Lemmas.Flow.Swizzle
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part132

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The three signed increments follow the low three bits of the current row. -/
def finalizeDeltas (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(6500, b32 (finalizeVectorDelta l g)), (6502, b32 (finalizeEvenDelta l g 1)),
    (6504, b32 (finalizeEvenDelta l g 2))]

private theorem rowMask (l : Launch) (g : Nat) (bit : Nat) (hb : (7 &&& bit) = bit) :
    (g % l.block) &&& bit = (rowOf l g % 8) &&& bit := by
  have hr : (g % l.block) % 8 = rowOf l g % 8 := by unfold rowOf; omega
  rw [← hr, ← Nat.and_two_pow_sub_one_eq_mod (x := g % l.block) (n := 3), Nat.and_assoc]
  rw [show 2 ^ 3 - 1 = 7 by decide, hb]

private def deltaInstr (dst pred : Nat) (stride : Int) : IntInstr :=
  ⟨.selp, .int .b 32, false, [some dst], [.imm stride, .imm (-stride), .reg pred]⟩

private theorem finalDeltaChoose {l : Launch} {g pc dst pred : Nat} {stride : Int}
    {t : TState} {F : List (Nat × Value)} (pick : Bool)
    (hc : kernel.code[pc]? = some ⟨none, .int (deltaInstr dst pred stride)⟩)
    (ht : At t pc F) (hPred : t.regs pred = some (.pred pick))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ dst) :
    ∃ u, run kernel [] l g 1 t = some u ∧ At u (pc + 1)
      ((dst, .bits 32 (truncBits 32 (BitVec.ofInt 64 (if pick then stride else -stride)))) ::
        F) := by
  let word := Value.bits 32 (truncBits 32 (BitVec.ofInt 64 (if pick then stride else -stride)))
  let u := next (setReg t dst word)
  have hRun : run kernel [] l g 1 t = some u := by
    apply run_local hc rfl ht
    rw [execLocalA_nil, execLocal_selp rfl]
    cases pick <;> simp [deltaInstr, execMove, DType.width, readReg, hPred, readValue, readBits,
      bind, Except.bind, pure, Except.pure, u, word, Value.bytes]
  exact ⟨u, hRun, ht.set hFresh⟩

private theorem finalDeltasFirst {l : Launch} {g : Nat} :
    Seg kernel [] l g 2 8448 [(1632, b32 (rowOf l g % 2))] 8450
      [(6500, b32 (finalizeVectorDelta l g))] := by
  intro t ht
  have hPred : Seg kernel [] l g 1 8448 [(1632, b32 (rowOf l g % 2))] 8449
      [(736, .pred (decide (rowOf l g % 2 = 0)))] := by
    intro s hs
    seg_fp hs using norm_cmp
  obtain ⟨v, hv, hV⟩ := hPred t ht
  obtain ⟨w, hw, hW⟩ := finalDeltaChoose (l := l) (g := g)
    (decide (rowOf l g % 2 = 0)) Flow.code_8449 (hV.mono (G := []) trivial)
    hV.2.2.2.2.1 (by simp)
  refine ⟨w, run_comp hv hw, ?_⟩
  unfold finalizeVectorDelta
  by_cases h : rowOf l g % 2 = 0
  · simp only [h, decide_true, ↓reduceIte] at hW ⊢
    exact hW
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte] at hW ⊢
    exact hW

private theorem finalDeltasEven {l : Launch} {g : Nat} (hc : g % l.block < 2 ^ 32) :
    Seg kernel [] l g 6 8450 [(1612, b32 (g % l.block))] 8456
      [(6502, b32 (finalizeEvenDelta l g 1)), (6504, b32 (finalizeEvenDelta l g 2))] := by
  intro t ht
  let tid := g % l.block
  let row := rowOf l g % 8
  let d32 := b32 (finalizeEvenDelta l g 1)
  have h2 : tid &&& 2 = row &&& 2 := rowMask l g 2 (by decide)
  have h4 : tid &&& 4 = row &&& 4 := rowMask l g 4 (by decide)
  have h2Lt : (row &&& 2) < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)
  have h4Lt : (row &&& 4) < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)
  have hTid32 : tid % 4294967296 = tid := Nat.mod_eq_of_lt hc
  have hTid64 : tid % 18446744073709551616 = tid := Nat.mod_eq_of_lt (by omega)
  have hPred2 : Seg kernel [] l g 2 8450 [(1612, b32 tid)] 8452
      [(737, .pred (decide (row &&& 2 = 0))), (1612, b32 tid)] := by
    intro s hs
    seg_fp hs using norm_cmp [hTid32, hTid64, h2]
  obtain ⟨v, hv, hV⟩ := hPred2 t ht
  obtain ⟨w, hw, hW⟩ := finalDeltaChoose (l := l) (g := g)
    (decide (row &&& 2 = 0)) Flow.code_8452 (hV.mono hV.2.2.2.2.2)
    hV.2.2.2.2.1 (by intro rv hr; rcases List.mem_singleton.mp hr with rfl; dsimp only; decide)
  have hW' : At w 8453 [(6502, d32), (1612, b32 tid)] := by
    have hWord : d32 = b32 (if row &&& 2 = 0 then 32 else 2 ^ 32 - 32) := rfl
    rw [hWord]
    by_cases h : row &&& 2 = 0
    · simp only [h, decide_true, ↓reduceIte] at hW ⊢
      exact hW
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte] at hW ⊢
      exact hW
  have hPred4 : Seg kernel [] l g 2 8453 [(6502, d32), (1612, b32 tid)] 8455
      [(738, .pred (decide (row &&& 4 = 0))), (6502, d32)] := by
    intro s hs
    seg_fp hs using norm_cmp [hTid32, hTid64, h4]
  obtain ⟨e, he, hE⟩ := hPred4 w hW'
  obtain ⟨u, hu, hU⟩ := finalDeltaChoose (l := l) (g := g)
    (decide (row &&& 4 = 0)) Flow.code_8455 (hE.mono hE.2.2.2.2.2)
    hE.2.2.2.2.1 (by intro rv hr; rcases List.mem_singleton.mp hr with rfl; dsimp only; decide)
  refine ⟨u, run_comp (run_comp (run_comp hv hw) he) hu,
    hU.mono ⟨hU.2.2.2.2.2.1, ?_, trivial⟩⟩
  have hWord : finalizeEvenDelta l g 2 = (if row &&& 4 = 0 then 64 else 2 ^ 32 - 64) := rfl
  rw [hWord]
  by_cases h : row &&& 4 = 0
  · simp only [h, decide_true, ↓reduceIte] at hU ⊢
    exact hU.2.2.2.2.1
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte] at hU ⊢
    exact hU.2.2.2.2.1

private theorem swizzleRowBase (base row : Nat) (hBase : base % 1024 = 0) :
    (base + 128 * row) ^^^ ((base + 128 * row) / 8 &&& 112) =
      base + 128 * row + 16 * (row % 8) := by
  have hEq : base + 128 * row = 128 * (8 * (base / 1024) + row) := by omega
  have hWord : (base + 128 * row) / 8 &&& 112 = 16 * (row % 8) := by
    rw [hEq]
    have hDiv : 128 * (8 * (base / 1024) + row) / 8 = (8 * (base / 1024) + row) <<< 4 := by
      rw [Nat.shiftLeft_eq]
      omega
    rw [hDiv, show 112 = 7 <<< 4 by decide, ← Nat.shiftLeft_and_distrib,
      show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
    omega
  rw [hWord]
  apply PTX.Proof.xor_eq_add 7
  · omega
  · omega

variable {p : Params} {l : Launch}

private theorem finalSwizzle {m : Mem0} {g : Nat} (hp : Pre p l m) :
    Seg kernel [] l g 8 8456
      [(1630, b32 (l.sharedBase + 128 * rowOf l g)),
        (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g))] 8464
      [(6498, b32 1), finalizeVectorFact l g 1 0, finalizeVectorFact l g 0 0] := by
  intro t ht
  let q := rowOf l g
  have hRow : q < 128 := Nat.mod_lt _ (by decide)
  have hs := hp.shared.2.1
  have ha := hp.shared.1
  have hS0 := swizzleRowBase (l.sharedBase + 3072) q (by omega)
  have hS1 := swizzleRowBase (l.sharedBase + 68608) q (by omega)
  have hB0 : l.sharedBase + 3072 + 128 * q < 2 ^ 32 := by omega
  have hB1 : l.sharedBase + 68608 + 128 * q < 2 ^ 32 := by omega
  have hB : l.sharedBase + 128 * q < 2 ^ 32 := by omega
  have hV0 : finalizeVectorFact l g 0 0 =
      (6511, b32 (l.sharedBase + 3072 + 128 * q + 16 * (q % 8))) := by
    simp [finalizeVectorFact, outputChunkLoc, sharedSlot, outputStoreAddrReg, Loc.at, q,
      Nat.add_assoc]
  have hV1 : finalizeVectorFact l g 1 0 =
      (6508, b32 (l.sharedBase + 68608 + 128 * q + 16 * (q % 8))) := by
    simp [finalizeVectorFact, outputChunkLoc, sharedSlot, outputStoreAddrReg, Loc.at, q,
      Nat.add_assoc]
  rw [hV0, hV1]
  have hX0 : ((l.sharedBase + 3072 + 128 * q) / 8 &&& 112) ^^^
        (l.sharedBase + 3072 + 128 * q) =
      l.sharedBase + 3072 + 128 * q + 16 * (q % 8) := (Nat.xor_comm ..).trans hS0
  have hX1 : ((l.sharedBase + 68608 + 128 * q) / 8 &&& 112) ^^^
        (l.sharedBase + 68608 + 128 * q) =
      l.sharedBase + 68608 + 128 * q + 16 * (q % 8) := (Nat.xor_comm ..).trans hS1
  have hSwap : l.sharedBase + 128 * q + 68608 = l.sharedBase + 68608 + 128 * q := by omega
  have hn : (l.sharedBase + 128 * q) % 4294967296 = l.sharedBase + 128 * q :=
    Nat.mod_eq_of_lt hB
  have hn0 : (l.sharedBase + 3072 + 128 * q) % 4294967296 = l.sharedBase + 3072 + 128 * q :=
    Nat.mod_eq_of_lt hB0
  have hn1 : (l.sharedBase + 68608 + 128 * q) % 4294967296 = l.sharedBase + 68608 + 128 * q :=
    Nat.mod_eq_of_lt hB1
  have hd0 : (l.sharedBase + 3072 + 128 * q) / 8 % 4294967296 =
      (l.sharedBase + 3072 + 128 * q) / 8 := Nat.mod_eq_of_lt (by omega)
  have hd1 : (l.sharedBase + 68608 + 128 * q) / 8 % 4294967296 =
      (l.sharedBase + 68608 + 128 * q) / 8 := Nat.mod_eq_of_lt (by omega)
  have hMask (a : Nat) : (a &&& 112) % 4294967296 = a &&& 112 :=
    Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (by decide : 112 < 2 ^ 32))
  dsimp only [q] at hn hSwap hn0 hn1 hd0 hd1 hX0 hX1
  seg_fp ht using
    nf_simp [nf_xor]
    all_goals (simp only [hn, hSwap, hn0, hn1, hd0, hd1, hMask, hX0, hX1]; rfl)

def finalizeLayoutFacts (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(6498, b32 1), finalizeVectorFact l g 1 0, finalizeVectorFact l g 0 0] ++ finalizeDeltas l g

private theorem finalizeLayoutCore {l : Launch} {g : Nat} {t : TState}
    (hLo : 8448 ≤ t.pc) (hHi : t.pc < 8464) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hCore : ((kernel.code.drop 8448).take 16).all (fun i => Assumptions.coreOp i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 8448).take 16 := by
      apply List.mem_of_getElem? (i := t.pc - 8448)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp hCore _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

/-- Execute the 16 local instructions that compute both stages' first swizzled vector
and the three signed address steps, preserving the supplied frame. -/
theorem finalizeLayoutRun {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {F : List (Nat × Value)} (ht : At t 8448 F) (hParity : (1632, b32 (rowOf l g % 2)) ∈ F)
    (hTid : (1612, b32 (g % l.block)) ∈ F) (hRow : (1630, b32 (l.sharedBase + 128 * rowOf l g)) ∈ F)
    (hBase : (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g)) ∈ F)
    (hWrite : ((kernel.code.drop 8448).take 16).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true) :
    ∃ u, run kernel Assumptions.all l g 16 t = some u ∧
      At u 8464 (finalizeLayoutFacts l g ++ F) := by
  have hFall : ((kernel.code.drop 8448).take 15).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hStable {a b : TState} {n : Nat} (ha : 8448 ≤ a.pc) (hb : a.pc + n ≤ 8464)
      (hr : run kernel [] l g n a = some b) (h : Holds a.regs F) : Holds b.regs F :=
    holdsSchedulerFrame h (fun _ hm => schedulerLocalFrame hWrite hFall hr ha hb hm)
      (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨v, hv, hV⟩ := finalDeltasFirst (l := l) (g := g) t
    (ht.mono ⟨holds_mem ht.2.2.2.2 hParity, trivial⟩)
  have hVF := hStable ht.1.ge (by rw [ht.1]; decide) hv ht.2.2.2.2
  have hBound : g % l.block < 2 ^ 32 := by rw [hp.block]; omega
  obtain ⟨w, hw, hW⟩ := finalDeltasEven (l := l) (g := g) hBound v
    (hV.mono ⟨holds_mem hVF hTid, trivial⟩)
  have hWF := hStable (by rw [hV.1]; decide) (by rw [hV.1]; decide) hw hVF
  obtain ⟨u, hu, hU⟩ := finalSwizzle (g := g) hp w
    (hW.mono ⟨holds_mem hWF hRow, holds_mem hWF hBase, trivial⟩)
  have hUF := hStable (by rw [hW.1]; decide) (by rw [hW.1]) hu hWF
  have hPreserve {r : Nat} (hr : r ∈ [6500, 6502, 6504]) : u.regs r = w.regs r := by
    have hWrt : ((kernel.code.drop 8456).take 8).all
        (fun i => [6500, 6502, 6504].all (fun r => !(writesRegs i.op).contains r)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact schedulerLocalFrame hWrt (by set_option maxRecDepth 100000 in kernel_rfl) hu
      hW.1.ge (by rw [hW.1]) hr
  have hOdd : w.regs 6500 = some (b32 (finalizeVectorDelta l g)) := by
    rw [schedulerLocalFrame (lo := 8450) (len := 6) (regs := [6500])
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hw hV.1.ge (by rw [hV.1]) (by simp)]
    exact hV.2.2.2.2.1
  have hDeltas : Holds u.regs (finalizeDeltas l g) := by
    exact ⟨(hPreserve (by simp)).trans hOdd,
      (hPreserve (by simp)).trans hW.2.2.2.2.1,
      (hPreserve (by simp)).trans hW.2.2.2.2.2.1, trivial⟩
  have hRun : run kernel [] l g 16 t = some u := run_comp (run_comp hv hw) hu
  have hA : run kernel Assumptions.all l g 16 t = some u :=
    schedulerLocalTransport (lo := 8448) (len := 16) hFall
      (fun h1 h2 => finalizeLayoutCore h1 h2) hRun ht.1.ge (by rw [ht.1])
  exact ⟨u, hA, hU.mono ((holds_append _ _ _).2
    ⟨(holds_append _ _ _).2 ⟨hU.2.2.2.2, hDeltas⟩, hUF⟩)⟩

/-- Compute both stages' first swizzled vector and the three signed address steps before
the statistics-slot release. All ABI and tile registers in the supplied frame survive. -/
theorem finalizeLayout {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t 8448 F) (hParity : (1632, b32 (rowOf l g % 2)) ∈ F)
    (hTid : (1612, b32 (g % l.block)) ∈ F) (hRow : (1630, b32 (l.sharedBase + 128 * rowOf l g)) ∈ F)
    (hBase : (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g)) ∈ F)
    (hWrite : ((kernel.code.drop 8448).take 16).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 8464 (finalizeLayoutFacts l g ++ F) := by
  obtain ⟨u, hu, hAt⟩ := finalizeLayoutRun hp ht hParity hTid hRow hBase hWrite
  exact ⟨u, run_rtg hu, hAt⟩

private def scaleParamLoad : MemAccess :=
  {kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
    addr := ⟨.param (param 12) false, 0⟩, dsts := [some 7134]}

set_option maxRecDepth 5000 in
private theorem loadScaleCode : kernel.code[8447]? = some ⟨none, .mem scaleParamLoad⟩ := by
  have hName : toString (12 : Nat) = "12" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (12 / 10 : Nat) = 1 by decide, show (12 % 10 : Nat) = 2 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 2) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_two.mpr rfl]
    rfl
  rw [Flow.code_8447]
  simp only [scaleParamLoad, param, hName]
  rfl

/-- The finalizer reloads the exact ABI log-base-two scale before either statistics read. -/
theorem finalizeScaleStep {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {F : List (Nat × Value)} (ht : At t 8447 F) (hFresh : ∀ rv ∈ F, rv.1 ≠ 7134) :
    ∃ u, Tau kernel Assumptions.all l g t u ∧
      At u 8448 ((7134, b32 p.scaleLog2Bits) :: F) := by
  let u := next (setReg t 7134 (b32 p.scaleLog2Bits))
  obtain ⟨hBits, hParam⟩ := hp.values (12, p.scaleLog2Bits) (by simp [Params.scalarWords])
  change l.params (param 12) = some (BitVec.ofNat 64 p.scaleLog2Bits) at hParam
  have hRaw : run kernel [] l g 1 t = some u := by
    apply run_local loadScaleCode rfl ht
    rw [execLocalA_nil, execLocal_mem rfl]
    simp only [scaleParamLoad, execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil,
      id_eq, hParam, DType.width, MemExt.extendBits_same, pure, Except.pure,
      truncBits_ofNat hBits (by decide)]
    rfl
  have hOut : out kernel Assumptions.all l g t = out kernel [] l g t := by
    apply Assumptions.out_all_eq_nil _ _ _ (ht.1.symm ▸ loadScaleCode) rfl
    all_goals rw [ht.1]; decide
  have hRun : run kernel Assumptions.all l g 1 t = some u := by
    simpa only [run, tauStep, hOut] using hRaw
  have hStep : tauStep kernel Assumptions.all l g t = some u := by
    cases h : tauStep kernel Assumptions.all l g t with
    | none => simp [run, h] at hRun
    | some v => simpa [run, h] using hRun
  exact ⟨u, tauStep_iff.mp hStep, ht.set hFresh⟩

/-- The ABI reload is a local unguarded parameter instruction. -/
theorem finalizeScaleInstruction :
    ∃ i, kernel.code[8447]? = some i ∧ i.guard = none ∧ i.op.isLocal = true :=
  ⟨_, loadScaleCode, rfl, rfl⟩

/-- From the post-rescale PC, load the ABI scale, establish both output layouts, and
release the second statistics slot before the first final statistics rendezvous. -/
theorem finalizeLayoutEntry {m : Mem0} {X : Execution} (hp : Pre p l m) {g pos : Nat} {t : TState}
    {F : List (Nat × Value)} (ht : At t 8447 F) (hParity : (1632, b32 (rowOf l g % 2)) ∈ F)
    (hTid : (1612, b32 (g % l.block)) ∈ F) (hRow : (1630, b32 (l.sharedBase + 128 * rowOf l g)) ∈ F)
    (hBase : (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g)) ∈ F)
    (hSlot : (1628, b32 (l.sharedBase + 200)) ∈ F) (hFresh : ∀ rv ∈ F, rv.1 ≠ 7134 ∧ rv.1 ≠ 9257)
    (hWrite : ((kernel.code.drop 8448).take 16).all
      (fun i => (7134 :: F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, X.get (g, pos) = some
        ⟨8464, .arrive (rescaleReuseLoc l g 0) 0 1 true .cta⟩ ∧
      At u 8465 (finalizeLayoutFacts l g ++ (7134, b32 p.scaleLog2Bits) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) none := by
  obtain ⟨s, hs, hS⟩ := finalizeScaleStep hp (g := g) ht (fun rv hm => (hFresh rv hm).1)
  obtain ⟨v, hv, hV⟩ := finalizeLayout hp hS
    (List.mem_cons_of_mem _ hParity) (List.mem_cons_of_mem _ hTid)
    (List.mem_cons_of_mem _ hRow) (List.mem_cons_of_mem _ hBase) hWrite
  have hLoc : l.sharedBase + 200 + 0 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase + 200 + 0) % 8 = 0 := by have := hp.shared.1; omega
  have hNoWrite (rv : Nat × Value)
      (hm : rv ∈ finalizeLayoutFacts l g ++ (7134, b32 p.scaleLog2Bits) :: F) :
      rv.1 ≠ 9257 := by
    rcases List.mem_append.mp hm with hm | hm
    · have hRegs := List.mem_map_of_mem (f := Prod.fst) hm
      intro he
      rw [he] at hRegs
      exact (of_decide_eq_true rfl : 9257 ∉ (finalizeLayoutFacts l g).map Prod.fst) hRegs
    · rcases List.mem_cons.mp hm with rfl | hm
      · change (7134 : Nat) ≠ 9257
        decide
      · exact (hFresh rv hm).2
  have hOut : out kernel Assumptions.all l g v = out kernel [] l g v := by
    apply Assumptions.out_all_eq_nil _ _ _ (hV.1.symm ▸ Flow.code_8464) rfl
    all_goals rw [hV.1]; decide
  have hSlotReg := holds_mem hV.2.2.2.2
    (List.mem_append.mpr (.inr (List.mem_cons_of_mem _ hSlot)))
  obtain ⟨u, hu, he, hU⟩ := observeCorrectionRelease (base := l.sharedBase + 200) (off := 0)
    hV hOut Flow.code_8464 hSlotReg hV.2.2.2.2.1 hLoc hAlign hNoWrite
    (hr.after_local ((Relation.ReflTransGen.single hs).trans hv))
  exact ⟨u, by simpa only [rescaleReuseLoc, Nat.add_zero, Fin.val_zero, Nat.mul_zero, Nat.sub_zero]
    using he, hu, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
