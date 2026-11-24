-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackStart
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
import Lemmas.Step.ProtectedReadProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem fallbackReadGate (l : Launch) (g : Nat) {first lane batch : Nat}
    (hi : first + lane < 2 ^ 31) (hb : batch < 2 ^ 31) :
    Seg kernel [] l g 3 3163 [(1218, b32 first), (1215, b32 lane), (7247, b32 batch)] 3166
      [(1219, b32 (first + lane)), (452, .pred (decide (batch < first + lane))),
        (7239, b32 0)] := by
  intro t ht
  have hi32 : first + lane < 2 ^ 32 := by omega
  have hf32 : first < 2 ^ 32 := by omega
  have hl32 : lane < 2 ^ 32 := by omega
  have hb32 : batch < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_add, truncBits_ofNat hf32 (by decide),
        truncBits_ofNat hl32 (by decide), truncBits_ofNat hi32 (by decide),
        truncBits_ofNat hb32 (by decide), compare, Option.getD_some,
        signedWord hi, signedWord hb, Int.ofNat_lt, gt_iff_lt]

private theorem fallbackReadAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {index : Nat} (hi : index ≤ p.batch) :
    Seg kernel [] l g 2 3167 [(1219, b32 index), (7506, b64 p.cuQBase)] 3169
      [(7890, b64 (p.cuQBase + 4 * index))] := by
  intro t ht
  have hb := hp.shape.2.1
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have h31 : index < 2 ^ 31 := by omega
  have h32 : index < 2 ^ 32 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hOff : 4 * index < 2 ^ 64 := by omega
  have hAddr : p.cuQBase + 4 * index < 2 ^ 64 := by omega
  have hFour : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hProduct : (index : Int) * 4 = ((4 * index : Nat) : Int) := by push_cast; omega
  seg_fp ht using simp only [b64, kind_s_beq_s, ↓reduceIte, hFour, signedWord h31,
    truncBits_ofNat h32 (by decide), truncBits_ofNat hOff (by decide),
    truncBits_ofNat hBase (by decide), hProduct, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    truncBits_ofNat hAddr (by decide)]

def fallbackReadAcc (p : Params) (index : Nat) : Acc :=
  {loc := globalLoc (p.cuQBase + 4 * index), size := 4}

private theorem fallbackReadOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g index : Nat} {t : TState} (hi : index ≤ p.batch)
    (ht : At t 3169 [(7890, b64 (p.cuQBase + 4 * index))]) :
    out kernel Assumptions.all l g t =
      .ev (.read (fallbackReadAcc p index) (afterLoad t [7239])) := by
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hSum : p.cuQBase + 4 * index < 2 ^ 64 := by omega
  have hAl := hp.alignment.2.2.2.2.2.2.2.2.1
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3169) rfl rfl]
  change Out.ev (loadTmpl Assumptions.all l g t .global false 32 [7239] 7890 0) = _
  exact congrArg Out.ev (loadTmpl_global (t := t) (w := 32)
    ht.2.1 ht.2.2.2.2.1 hSum (by decide) (by omega))

theorem fallbackLinear {l : Launch} {g lo n : Nat} {t u : TState}
    {F : List (Nat × Value)}
    (hLo : 3155 ≤ lo) (hHi : lo + n ≤ 3212) (ht : At t lo F)
    (hWrites : ((kernel.code.drop lo).take n).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hStraight : ((kernel.code.drop lo).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧ Holds u.regs F :=
  ⟨Mma.groupScanLocalRun .softmaxSelect hLo hHi ht.1 hStraight hr,
    holdsSchedulerFrame ht.2.2.2.2 (fun _ hr' =>
      schedulerLocalFrame hWrites hStraight hr ht.1.ge (by rw [ht.1]) hr')
      (fun _ hx => List.mem_map_of_mem hx)⟩

private theorem fallbackReadBranch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first cutoff : Nat} {warp : Fin 8} {t : TState} (hGroup : first + 31 < p.batch)
    (ht : At t 3163 (fallbackAdvanceFacts p l g warp first cutoff)) :
    let index := first + 31 + laneOf l g
    ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t w ∧
      At w (if p.batch < index then 3170 else 3167)
        ((7239, b32 0) :: (1219, b32 index) ::
      fallbackAdvanceFacts p l g warp first cutoff) := by
  dsimp only
  let lane := laneOf l g
  let index := first + 31 + lane
  let F := fallbackAdvanceFacts p l g warp first cutoff
  let carry := (1219, b32 index) :: F
  let guard := decide (p.batch < index)
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hIndex : index < 2 ^ 31 := by
    have hBatch := hp.shape.2.2.2.2.2
    dsimp only [index]
    omega
  have hAt : At t 3163 [(1218, b32 (first + 31)), (1215, b32 lane), (7247, b32 p.batch)] :=
    ht.mono ⟨ht.2.2.2.2.1, holds_lookup ht.2.2.2.2 rfl, holds_lookup ht.2.2.2.2 rfl, trivial⟩
  obtain ⟨v, hv, hV⟩ := (fallbackReadGate l g hIndex hp.shape.2.1).apply hAt
  obtain ⟨hvA, hFrame⟩ := fallbackLinear (F := F) (by decide) (by decide) ht
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hGate : At v 3166 ((452, .pred guard) :: (7239, b32 0) :: carry) :=
    hV.mono ⟨hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hV.2.2.2.2.1, hFrame⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_3166 guard hGate hGate.2.2.2.2.1 (by simp)
  have hwA := Mma.groupScanLocalRun .softmaxSelect (by decide) (by decide) hGate.1 rfl hw
  exact ⟨w, run_rtg (run_comp hvA hwA), by
    simpa only [guard, decide_eq_true_eq] using hW.mono hW.2.2.2.2.2⟩

private theorem fallbackReadReady {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first cutoff : Nat} {warp : Fin 8} {t : TState}
    (hIndex : first + 31 + laneOf l g ≤ p.batch)
    (ht : At t 3167 ((1219, b32 (first + 31 + laneOf l g)) ::
      fallbackAdvanceFacts p l g warp first cutoff)) :
    let index := first + 31 + laneOf l g
    ∃ a, At a 3169 ((1219, b32 index) :: fallbackAdvanceFacts p l g warp first cutoff) ∧
      Next kernel Assumptions.all l g t a
        (.read (fallbackReadAcc p index) (afterLoad a [7239])) := by
  obtain ⟨a, ha, hA⟩ := (fallbackReadAddress hp g hIndex).apply
    (ht.mono ⟨ht.2.2.2.2.1, holds_lookup ht.2.2.2.2 rfl, trivial⟩)
  obtain ⟨haA, haFrame⟩ := fallbackLinear (by decide) (by decide) ht
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide +kernel) ha
  exact ⟨a, hA.mono haFrame, run_rtg haA, fallbackReadOut hp hIndex hA⟩

private theorem fallbackReadReturns {l : Launch} {g first cutoff : Nat} {p : Params}
    {warp : Fin 8} {a : TState}
    (ha : At a 3169 ((1219, b32 (first + 31 + laneOf l g)) ::
      fallbackAdvanceFacts p l g warp first cutoff)) :
    let index := first + 31 + laneOf l g
    let word := b32 (drainCuQ p index)
    let u := afterLoad a [7239] (word.toBytes.map some)
    At u 3170 ((7239, word) :: (1219, b32 index) ::
      fallbackAdvanceFacts p l g warp first cutoff) := by
  dsimp only
  let word := b32 (drainCuQ p (first + 31 + laneOf l g))
  have hValue := rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
  have hOut : afterLoad a [7239] (word.toBytes.map some) = next (setReg a 7239 word) := by
    rw [afterLoad_ok ha.2.1 ha.2.2.1 hValue]
    simp [next, setReg, ha.2.1, ha.2.2.1]
  rw [hOut]
  exact ha.set (of_decide_eq_true rfl)

/-- The actual optional read preserves the group's search frame and advances the lane cursor
exactly when its cumulative-offset index is inside the allocated range. -/
theorem fallbackLaneRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g j first cutoff : Nat} {warp : Fin 8} {t : TState} {o : Option TState}
    (hGroup : first + 31 < p.batch)
    (ht : At t 3163 (fallbackAdvanceFacts p l g warp first cutoff))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) o)
    (hSuffix : (X.tr g).drop j ≠ []) (hCuQ : CuQReadsFromLaunch p X) :
    let index := first + 31 + laneOf l g
    let word := b32 (drainCuQ p index)
    ∃ u, At u 3170 ((7239, word) :: (1219, b32 index) ::
      fallbackAdvanceFacts p l g warp first cutoff) ∧
      (index ≤ p.batch → X.get (g, j) = some ⟨3169, .rd (fallbackReadAcc p index)
        (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if index ≤ p.batch then j + 1 else j)) o := by
  dsimp only
  let index := first + 31 + laneOf l g
  let word := b32 (drainCuQ p index)
  obtain ⟨w, hw, hW⟩ := fallbackReadBranch hp hGroup ht
  have hRun := hRun.after_local_nonempty hw hSuffix
  by_cases hi : first + 31 + laneOf l g ≤ p.batch
  · have hAt : At w 3167 ((1219, b32 index) :: fallbackAdvanceFacts p l g warp first cutoff) :=
      ⟨by simpa only [ite_eq_right (Nat.not_lt_of_ge hi)] using hW.1,
        (hW.mono hW.2.2.2.2.2).2⟩
    obtain ⟨a, ha, hn⟩ := fallbackReadReady hp hi hAt
    obtain ⟨_, u, he, ⟨bs, _, rfl, hU⟩, hTail⟩ := hn.continuing_at_nonempty (by
      rintro _ ⟨_, _, _, hBad⟩; cases hBad) hRun hSuffix
    obtain rfl := Option.some.inj hU
    rw [ha.1] at he
    have hIndex : index ≤ p.batch := hi
    have hBytes : bs = word.toBytes.map some := by
      simpa only [word, drainCuQ, ite_eq_left hIndex] using
        hCuQ index hi (g, j) bs ⟨3169, he⟩
    subst bs
    exact ⟨_, fallbackReadReturns (l := l) ha, fun _ => he,
      by simpa only [ite_eq_left hi] using hTail⟩
  · have hAt : At w 3170 ((7239, word) :: (1219, b32 index) ::
        fallbackAdvanceFacts p l g warp first cutoff) := by
      have hIndex : ¬ index ≤ p.batch := hi
      rw [show word = b32 0 by unfold word drainCuQ; rw [ite_eq_right hIndex]]
      simpa only [ite_eq_left (Nat.lt_of_not_ge hi)] using hW
    exact ⟨w, hAt, fun h => (hi h).elim, by simpa only [ite_eq_right hi] using hRun⟩

/-- Maximal traces perform the protected offset read precisely when the lane's index is live. -/
theorem fallbackLaneReadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g j first cutoff : Nat} {warp : Fin 8} {before t : TState} {o : Option TState}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch)
    (hProtect : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (ht : At t 3163 (fallbackAdvanceFacts p l g warp first cutoff))
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some before))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hTail : Run kernel Assumptions.all l g before ((X.tr g).drop j) o)
    (hPos : 0 < j) (hBound : j ≤ (X.tr g).length)
    (hReleased : j = (X.tr g).length → Step.Released l X g) :
    let index := first + 31 + laneOf l g
    let word := b32 (drainCuQ p index)
    let pos := if index ≤ p.batch then j + 1 else j
    ∃ before state, pos ≤ (X.tr g).length ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At state 3170 ((7239, word) :: (1219, b32 index) ::
        fallbackAdvanceFacts p l g warp first cutoff) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) before state ∧
      Run kernel Assumptions.all l g before ((X.tr g).drop pos) o ∧
      (index ≤ p.batch → X.get (g, j) = some ⟨3169, .rd (fallbackReadAcc p index)
        (word.toBytes.map some)⟩) := by
  dsimp only
  let index := first + 31 + laneOf l g
  let word := b32 (drainCuQ p index)
  obtain ⟨w, hw, hW⟩ := fallbackReadBranch hp hGroup ht
  by_cases hi : first + 31 + laneOf l g ≤ p.batch
  · have hAt : At w 3167 ((1219, b32 index) :: fallbackAdvanceFacts p l g warp first cutoff) :=
      ⟨by simpa only [ite_eq_right (Nat.not_lt_of_ge hi)] using hW.1,
        (hW.mono hW.2.2.2.2.2).2⟩
    obtain ⟨a, ha, hn⟩ := fallbackReadReady hp hi hAt
    have hn' : Next kernel Assumptions.all l g before a
        (.read (fallbackReadAcc p index) (afterLoad a [7239])) :=
      ⟨(hLocal.trans hw).trans hn.steps, hn.stop⟩
    obtain ⟨he, hPast', hTail'⟩ := Step.protected_read_of_maximal hMax hg (value := word)
      (show (fallbackReadAcc p index).size = word.bytes from rfl)
      (by
        intro k hk
        have hIndex : index ≤ p.batch := hi
        simp only [word, drainCuQ, ite_eq_left hIndex]
        exact hp.cuQ index hi k hk) (hProtect index hi)
      hn' hPast hTail hPos hBound hReleased
      (Assumptions.wf_snoc_initial hMax.1)
    rw [ha.1] at he
    rw [ite_eq_left hi]
    exact ⟨_, _, len_of_get he, Prologue.releasedIfLast he (by intro h; cases h),
      fallbackReadReturns (l := l) ha, hPast', .refl, hTail', fun _ => he⟩
  · rw [ite_eq_right hi]
    have hAt : At w 3170 ((7239, word) :: (1219, b32 index) ::
        fallbackAdvanceFacts p l g warp first cutoff) := by
      have hIndex : ¬ index ≤ p.batch := hi
      rw [show word = b32 0 by unfold word drainCuQ; rw [ite_eq_right hIndex]]
      simpa only [ite_eq_left (Nat.lt_of_not_ge hi)] using hW
    exact ⟨before, w, hBound, hReleased, hAt, hPast, hLocal.trans hw, hTail,
      fun h => (hi h).elim⟩

/-- The last lane is the scan sentinel and never contributes a request. -/
theorem fallbackLaneDown {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (hLane : (1215, b32 (laneOf l g)) ∈ F)
    (hWrites : ((kernel.code.drop 3170).take 1).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (ht : At t 3170 F) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 3171 ((453, .pred (decide (laneOf l g = 31))) :: F) := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  have h31 : (↑(truncBits 32 (BitVec.ofInt 64 31)).toNat : Int) = 31 := rfl
  have seg : Seg kernel [] l g 1 3170 [(1215, b32 lane)] 3171
      [(453, .pred (decide (lane = 31)))] := by
    intro s hs
    seg_fp hs using
      simp only [compare, Option.getD_some, truncBits_ofNat h32 (by decide),
        toNat_ofNat_lt h64, h31, Value.pred.injEq, decide_eq_decide]
      omega
  obtain ⟨u, hu, hU⟩ := seg.apply (ht.mono ⟨holds_mem ht.2.2.2.2 hLane, trivial⟩)
  obtain ⟨hRun, hFrame⟩ := fallbackLinear (by decide) (by decide) ht hWrites rfl hu
  exact ⟨u, hRun, hU.mono ⟨hU.2.2.2.2.1, hFrame⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
