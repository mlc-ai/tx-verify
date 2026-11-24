-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxStartup
public import Kernels.TmlFa4Fwd.Proof.Epilogue
public import Lemmas.Async.ReadSources
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.WarpScan
public import Lemmas.Kernel.ReadValue
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

def schedulerEntry (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) : List (Nat × Value) :=
  (7247, b32 p.batch) :: dispatchOutput p l g warp

def schedulerLane (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) (q : Nat) :
    List (Nat × Value) :=
  [(1215, b32 (laneOf l g)), (7237, b32 q)] ++ schedulerEntry p l g warp

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

variable {p : Params}

private theorem schedulerGate {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 4 3104 (schedulerEntry p l g warp)
      (if p.batch < laneOf l g then 3111 else 3108) (schedulerLane p l g warp 0) := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hLane32 : laneOf l g < 2 ^ 32 := by omega
  have hLane31 : laneOf l g < 2 ^ 31 := by omega
  have hBatch31 := hp.shape.2.1
  have hBatch32 : p.batch < 2 ^ 32 := by omega
  let F := schedulerLane p l g warp 0
  have hGate : Seg kernel Assumptions.all l g 3 3104 (schedulerEntry p l g warp)
      3107 ((438, .pred (decide (p.batch < laneOf l g))) :: F) := by
    intro t ht
    simp only [schedulerEntry, dispatchOutput, dispatchInput] at ht
    simp only [F, schedulerLane, schedulerEntry, dispatchOutput, dispatchInput,
      List.cons_append, List.nil_append]
    seg_fp ht using simp only [b32, compare, Option.getD_some,
      truncBits_ofNat hLane32 (by decide),
      truncBits_ofNat hBatch32 (by decide), signedWord hLane31, signedWord hBatch31, Int.ofNat_lt,
      show truncBits 32 (BitVec.ofInt 64 0) = 0#64 by decide]
  intro t ht
  obtain ⟨a, ha, hA⟩ := hGate t ht
  have hPred := hA.2.2.2.2.1
  obtain ⟨u, hu, hU⟩ := run_bra (A := []) (K := kernel) (L := l) (g := g)
    Flow.code_3107 (decide (p.batch < laneOf l g)) (hA.mono hA.2.2.2.2.2) hPred (by simp)
  have hTau : tauStep kernel Assumptions.all l g a = tauStep kernel [] l g a := by
    apply Assumptions.tauStep_all_eq_nil (by rw [hA.1]; decide)
      (by rw [hA.1]; exact Flow.code_3107) rfl
  have hStep : run kernel Assumptions.all l g 1 a = some u := by
    simpa only [run, hTau] using hu
  exact ⟨u, run_comp ha hStep, by simpa only [decide_eq_true_eq] using hU⟩

def laneCuQAcc (p : Params) (l : Launch) (g : Nat) : Acc :=
  {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}

private theorem schedulerAddr {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) (warp : Fin 8)
    (hLane : laneOf l g ≤ p.batch) :
    Seg kernel Assumptions.all l g 2 3108 (schedulerLane p l g warp 0) 3110
      ((7888, b64 (laneCuQAcc p l g).loc.addr) :: schedulerLane p l g warp 0) := by
  have hLaneLt : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hLane32 : laneOf l g < 2 ^ 32 := by omega
  have hLane64 : laneOf l g < 2 ^ 64 := by omega
  have hOff64 : 4 * laneOf l g < 2 ^ 64 := by omega
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hBase64 : p.cuQBase < 2 ^ 64 := by omega
  have hSum : p.cuQBase + 4 * laneOf l g < 2 ^ 64 := by omega
  intro t ht
  simp only [schedulerLane, schedulerEntry, dispatchOutput, dispatchInput,
    List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using simp only [b64, laneCuQAcc, globalLoc,
    truncBits_ofNat hLane32 (by decide), toNat_ofNat_lt hLane64, Nat.mul_comm (laneOf l g) 4,
    truncBits_ofNat hBase64 (by decide), truncBits_ofNat hOff64 (by decide), ← BitVec.ofNat_add,
    truncBits_ofNat hSum (by decide),
    show (some IType.u == some IType.s) = false by decide,
    show (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 by decide, Bool.false_eq_true, ite_false]

private theorem schedulerReadOut {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {F : List (Nat × Value)} (hLane : laneOf l g ≤ p.batch)
    (ht : At t 3110 ((7888, b64 (laneCuQAcc p l g).loc.addr) :: F)) :
    out kernel Assumptions.all l g t = .ev (.read (laneCuQAcc p l g) (afterLoad t [7237])) := by
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hSum : p.cuQBase + 4 * laneOf l g < 2 ^ 64 := by omega
  have hAl := hp.alignment.2.2.2.2.2.2.2.2.1
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3110) rfl rfl]
  change Out.ev (loadTmpl Assumptions.all l g t .global false 32 [7237] 7888 0) = _
  exact congrArg Out.ev (loadTmpl_global (t := t) (w := 32)
    ht.2.1 ht.2.2.2.2.1 hSum (by decide) (by omega))

private theorem schedulerAfterRead {l : Launch} {g : Nat} {b : TState} {warp : Fin 8}
    (hB : At b 3110 ((7888, b64 (laneCuQAcc p l g).loc.addr) :: schedulerLane p l g warp 0)) :
    let q := b32 (p.qOffset (laneOf l g))
    At (afterLoad b [7237] (q.toBytes.map some)) 3111
      (schedulerLane p l g warp (p.qOffset (laneOf l g))) := by
  dsimp only
  let q := b32 (p.qOffset (laneOf l g))
  have hValue := rebuild_scalar (v := q) (show 0 < 4 by decide) rfl
  have hReturn : afterLoad b [7237] (q.toBytes.map some) = next (setReg b 7237 q) := by
    rw [afterLoad_ok hB.2.1 hB.2.2.1 hValue]
    simp [next, setReg, hB.2.1, hB.2.2.1]
  rw [hReturn]
  have hKeep : At b 3110 ((1215, b32 (laneOf l g)) :: schedulerEntry p l g warp) :=
    hB.mono ⟨hB.2.2.2.2.2.1, hB.2.2.2.2.2.2.2⟩
  have hNext := hKeep.set (r := 7237) (v := q) (by
    simp [schedulerEntry, dispatchOutput, dispatchInput])
  exact hNext.mono ⟨hNext.2.2.2.2.2.1, hNext.2.2.2.2.1, hNext.2.2.2.2.2.2⟩

/-- A valid lane's first scheduler memory request reads its launch CuQ word. -/
theorem schedulerReadNext {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {warp : Fin 8} (ht : At t 3104 (schedulerEntry p l g warp)) (hLane : laneOf l g ≤ p.batch) :
    let q := p.qOffset (laneOf l g)
    ∃ u, u.pc = 3110 ∧ Next kernel Assumptions.all l g t u
      (.read (laneCuQAcc p l g) (afterLoad u [7237])) ∧
      At (afterLoad u [7237] ((b32 q).toBytes.map some)) 3111 (schedulerLane p l g warp q) := by
  obtain ⟨a, ha, hA⟩ := (schedulerGate hp g warp).rtg ht
  rw [ite_eq_right (Nat.not_lt.mpr hLane)] at hA
  obtain ⟨u, hu, hU⟩ := (schedulerAddr hp g warp hLane).rtg hA
  exact ⟨u, hU.1, ⟨ha.trans hu, schedulerReadOut hp hLane hU⟩, schedulerAfterRead hU⟩

/-- A lane past the batch sentinel advances to the first shuffle without a memory request. -/
theorem schedulerSkipLocal {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {warp : Fin 8} (ht : At t 3104 (schedulerEntry p l g warp)) (hLane : p.batch < laneOf l g) :
    ∃ u, At u 3111 (schedulerLane p l g warp 0) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨u, hu, hU⟩ := (schedulerGate hp g warp).rtg ht
  rw [ite_eq_left hLane] at hU
  exact ⟨u, hU, hu⟩

/-- The scheduler reaches its first shuffle with the actual protected cuQ value (or zero for a
lane beyond the batch sentinel). The event cursor includes the read exactly when it fires. -/
theorem schedulerFirstOperandPrefix {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i : Nat} {t : TState} {warp : Fin 8}
    {o : Option TState} (ht : At t 3104 (schedulerEntry p l g warp))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) o) (hNonempty : (X.tr g).drop i ≠ [])
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w dst bs, X.MemWrites w dst bs →
      ¬ dst.Covers ((laneCuQAcc p l g).loc.at k)) :
    let lane := laneOf l g
    let q := if lane ≤ p.batch then p.qOffset lane else 0
    let j := if lane ≤ p.batch then i + 1 else i
    ∃ u, At u 3111 (schedulerLane p l g warp q) ∧
      (lane ≤ p.batch → X.get (g, i) = some
        ⟨3110, .rd (laneCuQAcc p l g) ((b32 q).toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) o := by
  dsimp only
  obtain ⟨a, ha, hA⟩ := (schedulerGate hp g warp).rtg ht
  have hr := hRun.after_local_nonempty ha hNonempty
  by_cases hLane : laneOf l g ≤ p.batch
  · simp only [ite_eq_left hLane]
    have hA' : At a 3108 (schedulerLane p l g warp 0) := by
      simpa only [ite_eq_right (Nat.not_lt.mpr hLane)] using hA
    obtain ⟨b, hb, hB⟩ := (schedulerAddr hp g warp hLane).rtg hA'
    have hn : Next kernel Assumptions.all l g a b (.read (laneCuQAcc p l g) (afterLoad b [7237])) :=
      ⟨hb, schedulerReadOut hp hLane hB⟩
    obtain ⟨e, u, he, ⟨bs, _, rfl, hU⟩, hTail⟩ := hn.continuing_at_nonempty (by
      rintro _ ⟨_, _, _, hBad⟩
      cases hBad) hr hNonempty
    obtain rfl := Option.some.inj hU
    rw [hB.1] at he
    have hMem : X.MemReads (.thread (g, i)) (laneCuQAcc p l g) bs := .inl ⟨3110, he⟩
    let q := b32 (p.qOffset (laneOf l g))
    have hBytes : bs = q.toBytes.map some := by
      apply hX.launch_value hMem rfl (hProtected hLane)
      simpa [laneCuQAcc, q, b32, HasValue, Value.bytes] using hp.cuQ (laneOf l g) hLane
    subst bs
    exact ⟨_, schedulerAfterRead hB, fun _ => he, hTail⟩
  · simp only [ite_eq_right hLane]
    have hA' : At a 3111 (schedulerLane p l g warp 0) := by
      simpa only [ite_eq_left (Nat.lt_of_not_ge hLane)] using hA
    exact ⟨a, hA', fun h => (hLane h).elim, hr⟩

/-- At the scheduler's first shuffle the operand is the lane's cuQ word. -/
theorem schedulerFirstShuffleOut {l : Launch} {m : Mem0} (hp : Pre p l m) {g q : Nat} {t : TState}
    {warp : Fin 8} (ht : At t 3111 (schedulerLane p l g warp q)) :
    out kernel Assumptions.all l g t =
      .ev (.shfl .down (b32 q) 1 31 (fun word _ => next (setReg t 2683 word))) := by
  let k := fun (word : Value) (_ : Bool) => next (setReg t 2683 word)
  have hq : t.regs 7237 = some (b32 q) := ht.2.2.2.2.2.1
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3111) rfl rfl]
  change Out.ev (shflTmpl l g t .down 2683 none (.reg 7237) (.imm 1) (.imm 31) (.imm (-1))) =
    Out.ev (.shfl .down (b32 q) 1 31 k)
  simp [shflTmpl, readValue, readReg, hq, hBlock, b32, Value.bytes, readBits,
    pure, Except.pure, k]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Softmax
