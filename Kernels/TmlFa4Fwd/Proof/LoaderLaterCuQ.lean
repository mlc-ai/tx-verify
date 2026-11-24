-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderFallback
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Kernel.ReadValue
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

/-- The later group retains its initial work offset and the loader's launch operands. -/
def laterCarry (p : Params) (l : Launch) (g warp first : Nat) : List (Nat × Value) :=
  [(1076, b32 first), (7165, b32 first), (1075, b32 (g / l.block + 1)),
    (7160, b32 (tilePrefix p first * p.heads)), (7136, b32 p.heads)] ++ loaderCuQFacts p l g warp

def laterReadFacts (p : Params) (l : Launch) (g warp first : Nat) : List (Nat × Value) :=
  [(7161, b32 (drainCuQ p (first + laneOf l g))), (1077, b32 (first + laneOf l g)),
    (76, .pred (decide (laneOf l g = 31)))] ++ laterCarry p l g warp first

private theorem laterLaneGate (l : Launch) (g : Nat) {first lane batch : Nat}
    (hIndex : first + lane < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 3 239 [(1076, b32 first), (1073, b32 lane), (7170, b32 batch)] 242
      [(1077, b32 (first + lane)), (75, .pred (decide (batch < first + lane))),
       (7161, b32 0)] := by
  intro t ht
  have hIdx32 : first + lane < 2 ^ 32 := by omega
  have hFirst32 : first < 2 ^ 32 := by omega
  have hLane32 : lane < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  have hSign {n : Nat} (h : n < 2 ^ 31) :
      toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_add, truncBits_ofNat hFirst32 (by decide),
        truncBits_ofNat hLane32 (by decide), truncBits_ofNat hIdx32 (by decide),
        truncBits_ofNat hBatch32 (by decide), compare, Option.getD_some,
        hSign hIndex, hSign hBatch, Int.ofNat_lt, gt_iff_lt]

private theorem laterLaneAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {index : Nat} (hi : index ≤ p.batch) :
    Seg kernel [] l g 2 243 [(1077, b32 index), (7506, b64 p.cuQBase)] 245
      [(7513, b64 (p.cuQBase + 4 * index))] := by
  intro t ht
  have hBatch := hp.shape.2.1
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have h31 : index < 2 ^ 31 := by omega
  have hAddr : p.cuQBase + 4 * index < 2 ^ 64 := by omega
  have h32 : index < 2 ^ 32 := by omega
  have hOff : 4 * index < 2 ^ 64 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hI4 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hPr : (index : Int) * 4 = ((4 * index : Nat) : Int) := by push_cast; omega
  have hSign : toSigned 32 (BitVec.ofNat 64 index) = (index : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show index < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt h32, ite_eq_left h31]
  seg_fp ht using simp only [b64, kind_s_beq_s, ↓reduceIte, hI4, hSign,
    truncBits_ofNat h32 (by decide), truncBits_ofNat hOff (by decide),
    truncBits_ofNat hBase (by decide), hPr, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    truncBits_ofNat hAddr (by decide)]

private theorem laterLastLane (l : Launch) (g : Nat) {lane : Nat} (hl : lane < 32) :
    Seg kernel [] l g 1 246 [(1073, b32 lane)] 247 [(76, .pred (decide (lane = 31)))] := by
  intro t ht
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  have h31 : (↑(truncBits 32 (BitVec.ofInt 64 31)).toNat : Int) = 31 := rfl
  seg_fp ht using
    simp only [compare, Option.getD_some, truncBits_ofNat h32 (by decide),
      toNat_ofNat_lt h64, h31, Value.pred.injEq, decide_eq_decide]
    omega

/-- A later recorded event or a completed suffix supplies the optional load's continuation. -/
def LaterCuQDemand (X : Execution) (g pos : Nat) (ending : Option TState) : Prop :=
  ending = none ∨ ∃ (j : Nat) (e : Event), pos ≤ j ∧
    (245 < e.pc ∨ e.kind = .exit ∨ Execution.isShfl e = true) ∧ X.get (g, j) = some e

private theorem LaterCuQDemand.nonempty {l : Launch} {X : Execution} {g pos : Nat}
    {t : TState} {ending : Option TState} (h : LaterCuQDemand X g pos ending)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending) :
    (X.tr g).drop pos ≠ [] := by
  intro hEmpty
  rcases h with hDone | ⟨_, _, hBefore, _, he⟩
  · rw [hDone, hEmpty] at hr
    cases hr
  · exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
      ((List.drop_eq_nil_iff.mp hEmpty).trans hBefore)

private theorem LaterCuQDemand.advance {X : Execution} {g pos : Nat} {ending : Option TState}
    (h : LaterCuQDemand X g pos ending) {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g, pos) = some ⟨245, .rd a bytes⟩) : LaterCuQDemand X g (pos + 1) ending := by
  apply h.imp_right
  rintro ⟨j, e, hBefore, hKind, hGet⟩
  have hNe : pos ≠ j := by
    intro h
    subst j
    obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases hKind with h | h | h
    · exact (Nat.lt_irrefl 245) h
    · cases h
    · cases h
  exact ⟨j, e, by omega, hKind, hGet⟩

private theorem laterCuQBranch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp first : Nat} (hFirst : first < p.batch) {t : TState}
    (ht : At t 239 (laterCarry p l g warp first)) :
    let ix := first + laneOf l g
    ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t w ∧
      At w (if p.batch < ix then 246 else 243)
        ((75, .pred (decide (p.batch < ix))) :: (1077, b32 ix) :: (7161, b32 0) ::
          laterCarry p l g warp first) := by
  dsimp only
  let lane := laneOf l g
  let ix := first + lane
  let carry := laterCarry p l g warp first
  let regs := carry.map Prod.fst
  have hSize := hp.shape.2.2.2.2.2
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hIndex : ix < 2 ^ 31 := by omega
  have hAt : At t 239 [(1076, b32 first), (1073, b32 lane), (7170, b32 p.batch)] :=
    ht.mono ⟨ht.2.2.2.2.1, holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl, trivial⟩
  obtain ⟨v, hv, hV⟩ := laterLaneGate l g hIndex hp.shape.2.1 t hAt
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hKeep := holdsSchedulerFrame ht.2.2.2.2 hvFrame (fun _ h => List.mem_map_of_mem h)
  let guard := decide (p.batch < ix)
  have hGate : At v 242 ((75, .pred guard) :: (1077, b32 ix) :: (7161, b32 0) :: carry) :=
    hV.mono ⟨hV.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.2.1, hKeep⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_242 guard hGate hGate.2.2.2.2.1 (by simp)
  obtain ⟨hwA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hGate.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  exact ⟨w, run_rtg (run_comp hvA hwA), by
    simpa only [guard, decide_eq_true_eq] using hW⟩

private theorem laterCuQReadFrontier {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp first : Nat} {w : TState}
    (hi : first + laneOf l g ≤ p.batch)
    (hW : At w 243 ((75, .pred (decide (p.batch < first + laneOf l g))) ::
      (1077, b32 (first + laneOf l g)) :: (7161, b32 0) :: laterCarry p l g warp first)) :
    let ix := first + laneOf l g
    let a : Acc := {loc := globalLoc (p.cuQBase + 4 * ix), size := 4}
    ∃ s, s.pc = 245 ∧ Next kernel Assumptions.all l g w s (.read a (afterLoad s [7161])) ∧
      afterLoad s [7161] ((b32 (drainCuQ p ix)).toBytes.map some) =
        next (setReg s 7161 (b32 (drainCuQ p ix))) ∧
      At (next (setReg s 7161 (b32 (drainCuQ p ix)))) 246
        ((7161, b32 (drainCuQ p ix)) :: (1077, b32 ix) :: laterCarry p l g warp first) := by
  dsimp only
  let ix := first + laneOf l g
  let carry := laterCarry p l g warp first
  let regs := carry.map Prod.fst
  let word := b32 (drainCuQ p ix)
  have hwPc := hW.1
  have hFramed : Holds w.regs ((1077, b32 ix) :: carry) :=
    ⟨hW.2.2.2.2.2.1, hW.2.2.2.2.2.2.2⟩
  have hArg : At w 243 [(1077, b32 ix), (7506, b64 p.cuQBase)] :=
    ⟨hwPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
      hFramed.1, holds_lookup hFramed rfl, trivial⟩
  obtain ⟨s, hs, hS⟩ := laterLaneAddress hp g hi w hArg
  obtain ⟨hsA, hsFrame⟩ := loaderLinear (regs := 1077 :: regs) (by decide) (by decide) hwPc
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  have ha := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at ha
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  let acc : Acc := {loc := globalLoc (p.cuQBase + 4 * ix), size := 4}
  have hOut : out kernel Assumptions.all l g s = .ev (.read acc (afterLoad s [7161])) := by
    rw [loaderOutCore (by rw [hS.1]; decide) (by rw [hS.1]; decide)]
    rw [out_event hS.2.2.2.1 (by rw [hS.1]; exact Flow.code_245) rfl rfl]
    change Out.ev (loadTmpl [] l g s .global false 32 [7161] 7513 0) = _
    exact congrArg Out.ev (loadTmpl_global hS.2.1 hS.2.2.2.2.1 (by omega)
      (by decide) (by omega))
  have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
  have hState : afterLoad s [7161] (word.toBytes.map some) = next (setReg s 7161 word) := by
    rw [afterLoad_ok hS.2.1 hS.2.2.1 hRebuild]
    simp [next, setReg, hS.2.1, hS.2.2.1]
  have hRide := hS.mono (holdsSchedulerFrame hFramed hsFrame
    (fun _ hx => List.mem_map_of_mem hx))
  have hFresh (pair : Nat × Value) (hm : pair ∈ (1077, b32 ix) :: carry) : pair.1 ≠ 7161 := by
    intro e
    have hmem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [e] at hmem
    exact (of_decide_eq_true rfl : 7161 ∉ 1077 :: regs) hmem
  exact ⟨s, hS.1, ⟨run_rtg hsA, hOut⟩, hState, hRide.set (v := word) hFresh⟩

private theorem laterCuQSkip {p : Params} {l : Launch} {g warp first : Nat} {w : TState}
    (hi : ¬first + laneOf l g ≤ p.batch)
    (hW : At w 246 ((75, .pred (decide (p.batch < first + laneOf l g))) ::
      (1077, b32 (first + laneOf l g)) :: (7161, b32 0) :: laterCarry p l g warp first)) :
    At w 246 ((7161, b32 (drainCuQ p (first + laneOf l g))) ::
      (1077, b32 (first + laneOf l g)) :: laterCarry p l g warp first) := by
  have hWord : drainCuQ p (first + laneOf l g) = 0 := by simp [drainCuQ, hi]
  exact hW.mono ⟨hWord ▸ hW.2.2.2.2.2.2.1, hW.2.2.2.2.2.1, hW.2.2.2.2.2.2.2⟩

private theorem laterCuQReadLocal {p : Params} {l : Launch} {g warp first : Nat} {s : TState}
    (hS : At s 246 ((7161, b32 (drainCuQ p (first + laneOf l g))) ::
      (1077, b32 (first + laneOf l g)) :: laterCarry p l g warp first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 247 (laterReadFacts p l g warp first) := by
  let lane := laneOf l g
  let payload := (7161, b32 (drainCuQ p (first + lane))) ::
    (1077, b32 (first + lane)) :: laterCarry p l g warp first
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hArg : At s 246 [(1073, b32 lane)] :=
    hS.mono ⟨holds_lookup hS.2.2.2.2 rfl, trivial⟩
  obtain ⟨u, hu, hU⟩ := laterLastLane l g hLane s hArg
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := payload.map Prod.fst) (by decide) (by decide) hS.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hRide := holdsSchedulerFrame hS.2.2.2.2 huFrame (fun _ hx => List.mem_map_of_mem hx)
  exact ⟨u, run_rtg huA, hU.mono ⟨hRide.1, hRide.2.1, hU.2.2.2.2.1, hRide.2.2⟩⟩

/-- The later group's optional cuQ read is an actual event and supplies its launch word. -/
private theorem loaderLaterCuQReadyInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i warp first : Nat} (hFirst : first < p.batch) {t : TState}
    (ht : At t 239 (laterCarry p l g warp first))
    {ending : Option TState}
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hDemand : LaterCuQDemand X g i ending)
    (hProtected : ∀ j ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * j)).at k)) :
    let index := first + laneOf l g
    let word := b32 (drainCuQ p index)
    ∃ u, At u 247 (laterReadFacts p l g warp first) ∧
      (index ≤ p.batch → X.get (g, i) =
        some ⟨245, .rd {loc := globalLoc (p.cuQBase + 4 * index), size := 4}
          (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if index ≤ p.batch then i + 1 else i)) ending ∧
      LaterCuQDemand X g (if index ≤ p.batch then i + 1 else i) ending := by
  dsimp only
  let ix := first + laneOf l g
  let word := b32 (drainCuQ p ix)
  obtain ⟨w, hw, hW⟩ := laterCuQBranch hp hFirst ht
  have hMore := hDemand.nonempty hRun
  have hRest := hRun.after_local_nonempty hw hMore
  let afterPos := if ix ≤ p.batch then i + 1 else i
  let payload := (7161, word) :: (1077, b32 ix) :: laterCarry p l g warp first
  have hPath : ∃ s, At s 246 payload ∧
      (ix ≤ p.batch → X.get (g, i) =
        some ⟨245, .rd {loc := globalLoc (p.cuQBase + 4 * ix), size := 4}
          (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop afterPos) ending ∧
        LaterCuQDemand X g afterPos ending := by
    by_cases hi : ix ≤ p.batch
    · have hwPc : w.pc = 243 := by simpa [ix, Nat.not_lt_of_ge hi] using hW.1
      obtain ⟨s, hPc, hNext, hState, hAt⟩ := laterCuQReadFrontier hp hi
        (show At w 243 _ from ⟨hwPc, hW.2⟩)
      obtain ⟨_, _, he, ⟨bs, _, rfl, hu⟩, hTail⟩ := hNext.continuing_at_nonempty (by
        rintro e ⟨_, _, _, hBad⟩
        cases hBad) hRest hMore
      obtain rfl := Option.some.inj hu
      rw [hPc] at he
      let acc : Acc := {loc := globalLoc (p.cuQBase + 4 * ix), size := 4}
      have hRead : X.MemReads (.thread (g, i)) acc bs := .inl ⟨245, he⟩
      have hBytes : bs = word.toBytes.map some := by
        apply hX.launch_value hRead rfl (hProtected ix hi)
        simpa [word, drainCuQ, hi, acc, b32, HasValue, Value.bytes] using hp.cuQ ix hi
      subst bs
      rw [hState] at hTail
      exact ⟨_, hAt, fun _ => he, by
        simpa only [afterPos, ite_eq_left hi] using hTail, by
        simpa only [afterPos, ite_eq_left hi] using hDemand.advance he⟩
    · have hwPc : w.pc = 246 := by simpa [ix, Nat.lt_of_not_ge hi] using hW.1
      exact ⟨w, laterCuQSkip hi ⟨hwPc, hW.2⟩, fun h => (hi h).elim, by
        simpa only [afterPos, ite_eq_right hi] using hRest, by
          simpa only [afterPos, ite_eq_right hi] using hDemand⟩
  obtain ⟨s, hS, he, hTail, hRemaining⟩ := hPath
  obtain ⟨u, hu, hU⟩ := laterCuQReadLocal hS
  exact ⟨u, hU, he, hTail.after_local_nonempty hu (hRemaining.nonempty hTail), hRemaining⟩

private theorem laterDownTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp first : Nat} {t : TState} (ht : At t 247 (laterReadFacts p l g warp first)) :
    out kernel Assumptions.all l g t = .ev
      (.shfl .down (b32 (drainCuQ p (first + laneOf l g))) 1 31
        (fun value _ => next (setReg t 1728 value))) := by
  have hv := ht.2.2.2.2.1
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_247) rfl rfl]
  change Out.ev (shflTmpl l g t .down 1728 none (.reg 7161) (.imm 1) (.imm 31) (.imm (-1))) = _
  simp [shflTmpl, readValue, readReg, hv, hBlock, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

private theorem laterWarpReadFrame {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp first lane : Nat} (hg : g < l.threads) (hFirst : first + 31 < p.batch)
    (hl : lane < 32) {t : TState} (ht : At t 239 (loaderAdvancedFacts p l g warp first lane)) :
    At t 239 (laterCarry p l (warpLane l g lane) warp (first + 31)) := by
  let thread := warpLane l g
  let nextFirst := first + 31
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hStable := ht.2.2.2.2
  have hCta : thread lane / l.block = g / l.block :=
    (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  apply ht.mono
  have htFirst := hStable.2.1
  have htLimit := hStable.2.2.2.2.1
  change t.regs 7165 = some (b32 (min (first + 31) p.batch)) at htFirst
  change t.regs 7160 =
    some (b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)) at htLimit
  rw [Nat.min_eq_left (Nat.le_of_lt hFirst)] at htFirst
  rw [Nat.min_eq_right (Nat.le_of_lt hFirst)] at htLimit
  have htStop : t.regs 1075 = some (b32 (thread lane / l.block + 1)) := by
    rw [hCta]
    exact hStable.2.2.2.1
  exact ⟨hStable.1, htFirst, htStop, htLimit, hStable.2.2.2.2.2⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first + 31 < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 239 (loaderAdvancedFacts p l g warp first) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 247 < target.pc)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
include hp hX hg hFirst cur hProgress hPc hProtected

/-- Within the actual fallback loop, the next group's optional reads and down-shuffle
reconstruct the adjacent cuQ words lane by lane. -/
theorem loaderLaterWarpCuQRecorded :
    ∃ ready : SchedulerWarpAt l X g 248 (fun lane =>
      (1728, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp (first + 31)) (shuffles + 1) votes ends,
      ready.pos = (fun lane =>
        (if first + 31 + lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane) + 1) ∧
      (∀ lane < 32, first + 31 + lane ≤ p.batch →
        X.get (warpLane l g lane,cur.pos lane) = some ⟨245,.rd
          {loc := globalLoc (p.cuQBase + 4*(first+31+lane)),size := 4}
          ((b32 (p.qOffset (first+31+lane))).toBytes.map some)⟩) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g ready.pos src index target) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let nextFirst := first + 31
  let idx := fun lane => nextFirst + lane
  let pos := fun lane => if idx lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane
  let word := fun lane => b32 (drainCuQ p (idx lane))
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hRead (lane : Nat) (hl : lane < 32)
      (hDemand : LaterCuQDemand X (thread lane) (cur.pos lane) (ends lane)) :
      ∃ t, At t 247 (laterReadFacts p l (thread lane) warp nextFirst) ∧
        (idx lane ≤ p.batch → X.get (thread lane, cur.pos lane) =
          some ⟨245, .rd {loc := globalLoc (p.cuQBase + 4 * idx lane), size := 4}
            ((word lane).toBytes.map some)⟩) ∧
        Run kernel Assumptions.all l (thread lane) t
          ((X.tr (thread lane)).drop (pos lane)) (ends lane) ∧
        LaterCuQDemand X (thread lane) (pos lane) (ends lane) := by
    have hAt := laterWarpReadFrame hp hg hFirst hl (cur.checkpoint lane hl)
    have hRun := cur.continuation lane hl
    have hr := hRun.after_local_nonempty (cur.localSteps lane hl) (hDemand.nonempty hRun)
    obtain ⟨u, hu, he, hs, hNext⟩ :=
      loaderLaterCuQReadyInPrefix hp hX hFirst hAt hr hDemand hProtected
    rw [hLane lane hl] at he hs hNext
    exact ⟨u, hu, he, hs, hNext⟩
  have hDemand : ∀ lane < 32, LaterCuQDemand X (thread lane) (cur.pos lane) (ends lane) := by
    rcases hProgress with hDone | hFollow
    · exact fun lane hl => .inl (hDone lane hl)
    have hSrc : LaterCuQDemand X (thread src) (cur.pos src) (ends src) :=
      .inr ⟨index, target, hFollow.before, .inl (by omega), hFollow.get⟩
    obtain ⟨s, hs, hReadEvent, hsRun, hAfterRead⟩ := hRead src hFollow.lane hSrc
    have hRank : ((X.tr (thread src)).take (pos src)).countP Execution.isShfl = shuffles := by
      by_cases h : idx src ≤ p.batch
      · simp only [pos, ite_eq_left h, List.take_add_one]
        rw [show (X.tr (thread src))[cur.pos src]? = _ from hReadEvent h]
        simpa [Execution.isShfl] using cur.ordinals.shfl src hFollow.lane
      · simpa only [pos, ite_eq_right h] using cur.ordinals.shfl src hFollow.lane
    let step := fun value (_ : Bool) => next (setReg s 1728 value)
    have hn : Next kernel Assumptions.all l (thread src) s s (.shfl .down (word src) 1 31 step) :=
      ⟨.refl, by simpa only [word, idx, hLane src hFollow.lane] using laterDownTemplate hp hs⟩
    obtain ⟨recv, ok, he, hShuffle, _⟩ :=
      hn.shuffle_at_nonempty hsRun (hAfterRead.nonempty hsRun) hRank
    intro lane hl
    have hWarp := Step.sameWarp_trans (sameWarp_symm (Step.sameWarp_lane hBlock hg hFollow.lane).1)
      (Step.sameWarp_lane hBlock hg hl).1
    rcases Step.shfl_lane_of_ready hX he hShuffle hWarp with ⟨j, hPeer⟩ | ⟨j, pc, hExit, _⟩
    · obtain ⟨⟨pc, mode, a, b, c, value, good, hGet⟩, hCount⟩ := hPeer
      have hBefore : cur.pos lane ≤ j := by
        by_contra! hLate
        have hLe := Flow.countP_take_mono Execution.isShfl (X.tr (thread lane))
          (show j + 1 ≤ cur.pos lane by omega)
        have hSucc := Flow.countP_take_succ (p := Execution.isShfl) hGet rfl
        change ((X.tr (thread lane)).take (j + 1)).countP Execution.isShfl =
          ((X.tr (thread lane)).take j).countP Execution.isShfl + 1 at hSucc
        change ((X.tr (thread lane)).take j).countP Execution.isShfl = shuffles at hCount
        rw [hSucc, hCount, cur.ordinals.shfl lane hl] at hLe
        omega
      exact .inr ⟨j, ⟨pc, .shfl mode a b c value good⟩, hBefore, .inr (.inr rfl), hGet⟩
    · have hBefore : cur.pos lane ≤ j := by
        by_contra! hLate
        exact hFollow.noExit lane hl j hLate pc hExit
      exact .inr ⟨j, ⟨pc, .exit⟩, hBefore, .inr (.inl rfl), hExit⟩
  have hAll (lane : Nat) (hl : lane < 32) := hRead lane hl (hDemand lane hl)
  choose! state hAt hEvent hRun hNext using hAll
  have hOrd : WarpOrdinals l X g pos shuffles votes := by
    have keep (test : Event → Bool) (n : Nat)
        (hc : ∀ lane < 32, ((X.tr (thread lane)).take (cur.pos lane)).countP test = n)
        (hOrdinary : ∀ a bs, test ⟨245, .rd a bs⟩ = false) :
        ∀ lane < 32, ((X.tr (thread lane)).take (pos lane)).countP test = n := by
      intro lane hl
      by_cases h : idx lane ≤ p.batch
      · have he := hEvent lane hl h
        simp only [pos, ite_eq_left h, List.take_add_one]
        rw [show (X.tr (thread lane))[cur.pos lane]? = _ from he]
        simp [hOrdinary, hc lane hl]
      · simpa only [pos, ite_eq_right h] using hc lane hl
    exact ⟨keep _ _ cur.ordinals.shfl (fun _ _ => rfl), keep _ _ cur.ordinals.vote (fun _ _ => rfl)⟩
  let down : SchedulerWarpAt l X g 247
      (fun lane => laterReadFacts p l (thread lane) warp nextFirst) shuffles votes ends :=
    ⟨pos, state, state, hOrd, hRun, fun _ _ => .refl, hAt⟩
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
      (hm : pair ∈ laterReadFacts p l (thread lane) warp nextFirst) : pair.1 ≠ 1728 := by
    intro he
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hm'
    exact (of_decide_eq_true rfl : 1728 ∉
      (laterReadFacts p l (thread lane) warp nextFirst).map Prod.fst) hm'
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (state lane) =
        .ev (.shfl .down (word lane) 1 31
          (fun value _ => next (setReg (state lane) 1728 value))) := by
    simpa only [word, idx, hLane lane hl] using laterDownTemplate hp (hAt lane hl)
  have hAdvanceRead (h : WarpFollowsEvent l X g cur.pos src index target) :
      WarpFollowsEvent l X g down.pos src index target := by
    apply h.after
    · change pos src ≤ index
      by_cases hLoad : idx src ≤ p.batch
      · simp only [pos, ite_eq_left hLoad]
        have hGet := hEvent src h.lane hLoad
        have hNe : cur.pos src ≠ index := by
          intro hEq
          rw [hEq] at hGet
          have hSite := congrArg Event.pc (Option.some.inj (hGet.symm.trans h.get))
          change 245 = target.pc at hSite
          omega
        have := h.before
        omega
      · simpa only [pos, ite_eq_right hLoad] using h.before
    · intro lane hl k hLt hGe pc hExit
      by_cases hLoad : idx lane ≤ p.batch
      · have hGet := hEvent lane hl hLoad
        change k < pos lane at hLt
        simp only [pos, ite_eq_left hLoad] at hLt
        have hEq : k = cur.pos lane := by omega
        rw [hEq, hGet] at hExit
        cases hExit
      · change k < pos lane at hLt
        simp only [pos, ite_eq_right hLoad] at hLt
        omega
  obtain ⟨next, hPos, _, hAdvance⟩ := down.consumeShuffleToRecorded hp hX hg .down word
    (fun _ => 1) (fun _ => 31) hFresh hOut (hProgress.imp_right hAdvanceRead) hPc
  exact ⟨next,hPos,fun lane hl h => by simpa [word,idx,nextFirst,drainCuQ,h] using hEvent lane hl h,
    hAdvance ∘ hAdvanceRead⟩

theorem loaderLaterWarpCuQTo :
    ∃ ready : SchedulerWarpAt l X g 248 (fun lane =>
      (1728, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp (first + 31)) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g ready.pos src index target := by
  obtain ⟨ready,_,_,hAdvance⟩ :=
    loaderLaterWarpCuQRecorded hp hX hg hFirst cur hProgress hPc hProtected
  exact ⟨ready,hAdvance⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The fallback metadata and shuffle in a terminated trace. -/
theorem loaderLaterWarpCuQ (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first + 31 < p.batch)
    (cur : SchedulerWarpAt l X g 239 (loaderAdvancedFacts p l g warp first) shuffles votes)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) :
    Nonempty (SchedulerWarpAt l X g 248 (fun lane =>
      (1728, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp (first + 31)) (shuffles + 1) votes) := by
  obtain ⟨ready, _⟩ := loaderLaterWarpCuQTo hp hX hg hFirst cur
    (src := 0) (index := 0) (target := ⟨248, .exit⟩) (.inl (fun _ _ => rfl))
    (by decide) hProtected
  exact ⟨ready⟩

private theorem laterLaneCuQOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g warp first pos : Nat} (hg : g < l.threads) (hFirst : first < p.batch)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {before t : TState}
    {ending : Option TState} (ht : At t 239 (laterCarry p l g warp first))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hTail : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending) (hPositive : 0 < pos)
    (hBound : pos ≤ (X.tr g).length) (hReleased : pos = (X.tr g).length → Step.Released l X g) :
    let ix := first + laneOf l g
    let after := if ix ≤ p.batch then pos + 1 else pos
    ∃ u ready, after ≤ (X.tr g).length ∧ (after = (X.tr g).length → Step.Released l X g) ∧
      At ready 247 (laterReadFacts p l g warp first) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take after) (some u) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) u ready ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop after) ending ∧
      (ix ≤ p.batch → X.get (g, pos) =
        some ⟨245, .rd {loc := globalLoc (p.cuQBase + 4 * ix), size := 4}
          ((b32 (drainCuQ p ix)).toBytes.map some)⟩) := by
  dsimp only
  let ix := first + laneOf l g
  obtain ⟨w, hw, hW⟩ := laterCuQBranch hp hFirst ht
  by_cases hi : ix ≤ p.batch
  · have hWpc : w.pc = 243 := by simpa [ix, Nat.not_lt_of_ge hi] using hW.1
    obtain ⟨s, hSite, hNext, hState, hAt⟩ :=
      laterCuQReadFrontier hp hi (show At w 243 _ from ⟨hWpc, hW.2⟩)
    let a : Acc := {loc := globalLoc (p.cuQBase + 4 * ix), size := 4}
    let word := b32 (drainCuQ p ix)
    have hAtRead : Next kernel Assumptions.all l g before s (.read a (afterLoad s [7161])) :=
      ⟨(hSteps.trans hw).trans hNext.steps,hNext.stop⟩
    obtain ⟨he,hPast,hRest⟩ := Step.protected_read_of_maximal hMax hg
      (show a.size = word.bytes from rfl)
      (by
        intro k hk
        simp only [word, drainCuQ, ite_eq_left hi]
        exact hp.cuQ ix hi k hk) (hProtected ix hi)
      hAtRead hPrefix hTail hPositive hBound hReleased
      (Assumptions.wf_snoc_initial hMax.1)
    obtain ⟨ready,hReadySteps,hReady⟩ := laterCuQReadLocal hAt
    rw [hState] at hPast hRest
    rw [hSite] at he
    rw [ite_eq_left hi]
    exact ⟨_,ready,len_of_get he,releasedIfLast he (by intro h; cases h),hReady,hPast,
      hReadySteps,hRest,fun _ => he⟩
  · have hWpc : w.pc = 246 := by simpa [ix, Nat.lt_of_not_ge hi] using hW.1
    obtain ⟨ready,hReadySteps,hReady⟩ := laterCuQReadLocal (laterCuQSkip hi ⟨hWpc,hW.2⟩)
    rw [ite_eq_right hi]
    exact ⟨before,ready,hBound,hReleased,hReady,hPrefix,
      (hSteps.trans hw).trans hReadySteps,hTail,fun h => (hi h).elim⟩

/-- A later loader group obtains its cumulative offsets and adjacent lane word in a maximal run. -/
theorem loaderLaterWarpCuQOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g warp first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first + 31 < p.batch)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 239 (loaderAdvancedFacts p l g warp first)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 248 (fun lane =>
      (1728, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp (first + 31)) (shuffles + 1) votes ends) := by
  classical
  let nextFirst := first + 31
  let idx := fun lane => nextFirst + lane
  let thread := warpLane l g
  let pos := fun lane => if idx lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane
  let word := fun lane => b32 (drainCuQ p (idx lane))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hAll (lane : Nat) (hl : lane < 32) :
      ∃ before ready, pos lane ≤ (X.tr (thread lane)).length ∧
        (pos lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
        At ready 247 (laterReadFacts p l (thread lane) warp nextFirst) ∧
        Run kernel Assumptions.all l (thread lane) {}
          ((X.tr (thread lane)).take (pos lane)) (some before) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before ready ∧
        Run kernel Assumptions.all l (thread lane) before
          ((X.tr (thread lane)).drop (pos lane)) (ends lane) ∧
        (idx lane ≤ p.batch → X.get (thread lane, cur.pos lane) =
          some ⟨245, .rd {loc := globalLoc (p.cuQBase + 4 * idx lane), size := 4}
            ((word lane).toBytes.map some)⟩) := by
    have hAt := laterWarpReadFrame hp hg hFirst hl (cur.checkpoint lane hl)
    have hRead := laterLaneCuQOfMaximal hp hMax
      (Step.sameWarp_lane hBlock hg hl).1.1.2.1 hFirst hProtected hAt
      (cur.recorded lane hl) (cur.localSteps lane hl) (cur.continuation lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
    have hLane' : laneOf l (g - laneOf l g + lane) = lane := hLane lane hl
    dsimp only at hRead
    rw [hLane'] at hRead
    exact hRead
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! before state hBound hRelease hAt hPast hTau hRun hEvent using hAll
  have hOrd : WarpOrdinals l X g pos shuffles votes := by
    have keep (test : Event → Bool) (n : Nat)
        (hc : ∀ lane < 32, ((X.tr (thread lane)).take (cur.pos lane)).countP test = n)
        (hOrdinary : ∀ a bs, test ⟨245, .rd a bs⟩ = false) :
        ∀ lane < 32, ((X.tr (thread lane)).take (pos lane)).countP test = n := by
      intro lane hl
      by_cases h : idx lane ≤ p.batch
      · simp only [pos, ite_eq_left h, List.take_add_one]
        rw [show (X.tr (thread lane))[cur.pos lane]? = _ from hEvent lane hl h]
        simp [hOrdinary, hc lane hl]
      · simpa only [pos, ite_eq_right h] using hc lane hl
    exact ⟨keep _ _ cur.ordinals.shfl (fun _ _ => rfl), keep _ _ cur.ordinals.vote (fun _ _ => rfl)⟩
  let down : SchedulerWarpReached l X g 247
      (fun lane => laterReadFacts p l (thread lane) warp nextFirst) shuffles votes ends :=
    ⟨⟨pos,before,state,hOrd,hRun,hTau,hAt⟩,fun lane hl => by
      have := cur.positive lane hl
      dsimp only [pos]
      split_ifs <;> omega,hBound,hRelease,hPast⟩
  apply down.consumeShuffle (dst := 1728) hp hMax hg .down word (fun _ => 1) (fun _ => 31)
  · intro lane _ pair hm he
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hm'
    exact (of_decide_eq_true rfl : 1728 ∉
      (laterReadFacts p l (thread lane) warp nextFirst).map Prod.fst) hm'
  · intro lane hl
    simpa only [word, idx, hLane lane hl] using laterDownTemplate hp (hAt lane hl)

end
end PTX.Kernels.TmlFa4Fwd.Loader
