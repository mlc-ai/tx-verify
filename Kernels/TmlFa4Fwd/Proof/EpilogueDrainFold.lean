-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueExitLoop
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Lemmas.Flow.WarpScan
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The scan's two arithmetic instructions fall through and update the selected word
and its running total. -/
theorem drainFoldCode (later : Bool) (stage : Fin 5) :
    ∃ a b : Instr,
      kernel.code[drainScanPc later stage + 1]? = some a ∧
      kernel.code[drainScanPc later stage + 2]? = some b ∧
      writesRegs a.op = [drainScanDst later stage + 1] ∧
      writesRegs b.op = [drainScanSum later stage] ∧
      (∀ pc, nextPc a.op pc = pc + 1) ∧ (∀ pc, ¬ BrxTarget a.op pc) := by
  cases later <;> fin_cases stage
  · exact ⟨_, _, Flow.code_3010, Flow.code_3011, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3013, Flow.code_3014, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3016, Flow.code_3017, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3019, Flow.code_3020, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3022, Flow.code_3023, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3067, Flow.code_3068, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3070, Flow.code_3071, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3073, Flow.code_3074, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3076, Flow.code_3077, rfl, rfl, fun _ => rfl, fun _ h => h⟩
  · exact ⟨_, _, Flow.code_3079, Flow.code_3080, rfl, rfl, fun _ => rfl, fun _ h => h⟩

private theorem drainScan_distinct (later : Bool) (stage : Fin 5) :
    drainScanDst later stage ≠ drainScanSrc later stage ∧
      drainScanDst later stage ≠ drainScanGuardReg later stage := by
  cases later <;> fin_cases stage <;> decide

/-- Invoking the two local instructions after an up shuffle folds two disjoint lane windows.
The lane and source words are bounded by the request prefix's signed head count. -/
theorem drainWarpFold {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {A : List Assumption} (later : Bool) (stage : Fin 5) (g : Nat) {first lane : Nat}
    (hf : first ≤ p.batch) (hl : lane < 32) (t u : TState) (e : Event)
    (hAt : At t (drainScanPc later stage)
      [(drainScanGuardReg later stage, .pred (drainScanGuard stage lane)),
       (drainScanSrc later stage,
        b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))])
    (hFire : Fires t.pc
      (.shfl .up (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))
        (2 ^ stage.val) 0 (fun v _ => next (setReg t (drainScanDst later stage) v))) e (some u))
    (hValue : ∃ ok, e = ⟨t.pc, .shfl .up
      (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))
      (2 ^ stage.val) 0
      (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
        (shflSource .up lane (2 ^ stage.val) 0).1)) ok⟩)
    (hModel : ∀ {s : TState}, drainScanPc later stage + 1 ≤ s.pc →
      s.pc ≤ drainScanPc later stage + 2 → out kernel A l g s = out kernel [] l g s) :
    ∃ v, run kernel A l g 2 u = some v ∧ At v (drainScanPc later stage + 3)
      [(drainScanSum later stage,
        b32 (prefixWindow (groupLaneTiles p first) (2 * 2 ^ stage.val) lane))] ∧
      ∀ r, r ∉ [drainScanDst later stage, drainScanDst later stage + 1,
        drainScanSum later stage] → v.regs r = t.regs r := by
  let xs := groupLaneTiles p first
  let width := 2 ^ stage.val
  let source := (shflSource .up lane width 0).1
  have hWidth : width < 32 := Nat.pow_lt_pow_right (by decide) stage.isLt
  have hs : source < 32 := by
    dsimp [source]
    rw [shflSource_up hWidth]
    split
    · exact lt_of_le_of_lt (Nat.sub_le _ _) hl
    · exact hl
  have hsum : prefixWindow xs width lane + prefixWindow xs width source < 2 ^ 32 := by
    have h1 := hp.groupWindow_signed hf hl width
    have h2 := hp.groupWindow_signed hf hs width
    change prefixWindow xs width lane < 2 ^ 31 at h1
    change prefixWindow xs width source < 2 ^ 31 at h2
    omega
  obtain ⟨recv, ok, he, hu⟩ := hFire
  obtain ⟨expect, hE⟩ := hValue
  rw [he] at hE
  obtain ⟨rfl, -⟩ := by
    simpa only [Event.mk.injEq, Kind.shfl.injEq, true_and] using hE
  obtain rfl := Option.some.inj hu
  have hReg : t.regs (drainScanGuardReg later stage) =
      some (.pred (drainScanGuard stage lane)) := holds_mem hAt.2.2.2.2 (by simp)
  have hOld : t.regs (drainScanSrc later stage) = some (b32 (prefixWindow xs width lane)) :=
    holds_mem hAt.2.2.2.2 (by simp [xs, width])
  obtain ⟨hSource, hGuard⟩ := drainScan_distinct later stage
  have hNext : At (next (setReg t (drainScanDst later stage)
      (b32 (prefixWindow xs width source)))) (drainScanPc later stage + 1)
      [(drainScanGuardReg later stage, .pred (drainScanGuard stage lane)),
       (drainScanSrc later stage, b32 (prefixWindow xs width lane)),
       (drainScanDst later stage, b32 (prefixWindow xs width source))] := by
    refine ⟨by simp [next, setReg, hAt.1], hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, ?_⟩
    simp [Holds, next, setReg, Ne.symm hGuard, Ne.symm hSource, hReg, hOld]
  obtain ⟨v, hr, hv⟩ := drainScanFold later stage l g xs hl hsum _ hNext
  obtain ⟨a, b, ha, hb, hra, hrb, hp, hbrx⟩ := drainFoldCode later stage
  rw [← hNext.1] at ha
  rw [show drainScanPc later stage + 2 =
    (next (setReg t (drainScanDst later stage) (b32 (prefixWindow xs width source)))).pc + 1 by
      rw [hNext.1]] at hb
  refine ⟨v, run_two_core_transport ha (hp _) hbrx (fun hs => ?_) hr, hv, ?_⟩
  · rw [hNext.1] at hs
    exact hModel (by omega) (by omega)
  · intro r hReg
    have hFrame := run_two_core_frame ha hb (hp _) hbrx hr r
      (by simpa [hra] using fun h => hReg (by simp [h]))
      (by simpa [hrb] using fun h => hReg (by simp [h]))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hReg
    simpa [next, setReg, hReg.1] using hFrame

/-- An actual drain shuffle receives its corresponding lane's operand and extends the prefix
window. The following local steps preserve the remaining lane scan guards. -/
theorem drainScanObserved {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (later : Bool) (stage : Fin 5) {g i j ordinal first : Nat} (hf : first ≤ p.batch)
    (t : TState) (recv peerRecv : Value) (ok peerOk : Bool) :
    let lane := laneOf l g
    let source := (shflSource .up lane (2 ^ stage.val) 0).1
    let part := prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
    let ev := ⟨drainScanPc later stage, .shfl .up (b32 (part lane)) (2 ^ stage.val) 0 recv ok⟩
    At t (drainScanPc later stage)
      [(drainScanGuardReg later stage, .pred (drainScanGuard stage lane)),
       (drainScanSrc later stage, b32 (part lane))] →
    X.get (g, i) = some ev → X.ShflK (g, i) ordinal →
    X.get (g - lane + source, j) = some ⟨drainScanPc later stage,
      .shfl .up (b32 (part source)) (2 ^ stage.val) 0 peerRecv peerOk⟩ →
    X.ShflK (g - lane + source, j) ordinal → ¬ ShflExited X (g - lane + source) ordinal →
    ∃ u v, EStep kernel Assumptions.all l g t ev (some u) ∧
      run kernel Assumptions.all l g 2 u = some v ∧ At v (drainScanPc later stage + 3)
      [(drainScanSum later stage,
        b32 (prefixWindow (groupLaneTiles p first) (2 * 2 ^ stage.val) lane))] ∧
      ∀ r, r ∉ [drainScanDst later stage, drainScanDst later stage + 1,
        drainScanSum later stage] → v.regs r = t.regs r := by
  dsimp only
  intro ht hE hK hPeer hPeerK hLive
  have hPCLo : 3009 ≤ drainScanPc later stage := by
    cases later <;> simp [drainScanPc]; omega
  have hPCHi : drainScanPc later stage ≤ 3078 := by
    have := stage.isLt
    cases later <;> simp [drainScanPc] <;> omega
  have hEq := shfl_source_value hX hE hK hPeer hPeerK hLive
  have hReg := holds_mem ht.2.2.2.2 (by right; left)
  have hCore := drainScanTemplate hp later stage g t _ ht.1 ht.2.2.2.1 hReg
  have hModel {s : TState} (hlo : drainScanPc later stage ≤ s.pc)
      (hhi : s.pc ≤ drainScanPc later stage + 2) :
      out kernel Assumptions.all l g s = out kernel [] l g s :=
    epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
  rw [← hModel (by rw [ht.1]) (by rw [ht.1]; omega)] at hCore
  let u := next (setReg t (drainScanDst later stage) recv)
  have hFire : Fires t.pc
      (.shfl .up (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) (laneOf l g)))
        (2 ^ stage.val) 0 (fun v _ => next (setReg t (drainScanDst later stage) v)))
      ⟨drainScanPc later stage, .shfl .up
        (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) (laneOf l g)))
        (2 ^ stage.val) 0 recv ok⟩ (some u) :=
    ⟨recv, ok, by rw [ht.1], rfl⟩
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨v, hv, hAt, hFrame⟩ := drainWarpFold hp later stage g hf hLane t u _ ht hFire
    ⟨ok, by rw [ht.1, hEq.1]⟩ (fun hlo hhi => hModel (by omega) hhi)
  exact ⟨u, v, ⟨_, hCore, hFire⟩, hv, hAt, hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
