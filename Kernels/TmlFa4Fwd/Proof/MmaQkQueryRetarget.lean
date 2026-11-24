-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private def otherQueryStage (stage : Fin 2) : Fin 2 := if stage = 0 then 1 else 0

private def scratchLow (block : Fin 4) : Nat := qkBReg block - 4

private def scratchHigh (block : Fin 4) : Nat := qkBReg block - 2

private def queryPackGap (step : Fin 8) : Nat := if step.val = 0 then 0 else 1

private def queryPackPc (block : Fin 4) (step : Fin 8) : Nat :=
  qkSetupPc block step + 2 + queryPackGap step

private def shiftedQueryLow (block : Fin 4) (lo : Nat) : Value :=
  .bits 32 (truncBits 32
    (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (lo + 2 ^ 32 * 0x40004040))) +
      truncBits 32 (BitVec.ofInt 64 (qkRetargetOffset block))))

private def extractedQueryHigh (lo : Nat) : Value :=
  .bits 32 (truncBits 32
    (BitVec.ofNat 64 ((BitVec.ofNat 64 (lo + 2 ^ 32 * 0x40004040)).toNat / 2 ^ 32)))

private def queryScratch (block : Fin 4) (lo : Nat) : List (Nat × Value) :=
  [(scratchLow block, shiftedQueryLow block lo), (scratchHigh block, extractedQueryHigh lo)]

set_option maxRecDepth 100000 in
private theorem queryUnpackAndShift {l : Launch} {g : Nat} (block : Fin 4) (step : Fin 8)
    (lo : Nat) :
    Seg kernel [] l g 2 (qkSetupPc block step)
      [(9624 + step.val, b64 (lo + 2 ^ 32 * 0x40004040))]
      (qkSetupPc block step + 2) (queryScratch block lo) := by
  fin_cases block <;> fin_cases step <;> intro t ht <;>
    seg_fp ht using
      (simp only [shiftedQueryLow, extractedQueryHigh,
        qkRetargetOffset, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
        ↓reduceIte])

set_option maxRecDepth 100000 in
private theorem queryPack {l : Launch} {g : Nat} (block : Fin 4) (step : Fin 8)
    {lo : Nat} (hLo : lo < 2 ^ 32) (hBack : 2048 ≤ lo) (hWide : lo + 2048 < 2 ^ 32) :
    Seg kernel [] l g 1 (queryPackPc block step) (queryScratch block lo)
      (queryPackPc block step + 1)
      [(9624 + step.val, b64 (qkRetargetLow block lo + 2 ^ 32 * 0x40004040))] := by
  have hWord := retargetPacked block hLo hBack hWide
  fin_cases block <;> fin_cases step <;> intro t ht <;>
    seg_fp ht using
      (simp only [shiftedQueryLow, extractedQueryHigh, qkRetargetOffset] at hWord ⊢; exact hWord)

private theorem takeRun {l : Launch} {g total n : Nat} {t u : TState}
    (hRun : run kernel [] l g total t = some u) (hN : n ≤ total) :
    ∃ s, run kernel [] l g n t = some s ∧ run kernel [] l g (total - n) s = some u := by
  rw [← Nat.add_sub_of_le hN, run_add] at hRun
  cases hs : run kernel [] l g n t with
  | none => simp [hs] at hRun
  | some s => exact ⟨s, rfl, by simpa only [hs, Option.bind_some] using hRun⟩

private theorem setupPcBounds (block : Fin 4) (step : Fin 8) :
    qkPc block - 40 ≤ qkSetupPc block step ∧
      queryPackPc block step + 1 ≤ qkPc block := by
  fin_cases block <;> fin_cases step <;> decide

private def untouched (r lo n : Nat) : Prop :=
  ((kernel.code.drop lo).take n).all (fun i => !(writesRegs i.op).contains r) = true ∧
  ((kernel.code.drop lo).take (n - 1)).all (fun i => schedulerFallsThrough i.op) = true

set_option maxRecDepth 100000 in
private theorem inputPreserved (block : Fin 4) (step : Fin 8) :
    untouched (9624 + step.val) (qkPc block - 40)
      (qkSetupPc block step - (qkPc block - 40)) := by
  fin_cases block <;> fin_cases step <;> exact ⟨by kernel_rfl,by kernel_rfl⟩

set_option maxRecDepth 100000 in
private theorem lowPreserved (block : Fin 4) (step : Fin 8) :
    untouched (scratchLow block) (qkSetupPc block step + 2) (queryPackGap step) := by
  fin_cases block <;> fin_cases step <;> exact ⟨by kernel_rfl,by kernel_rfl⟩

set_option maxRecDepth 100000 in
private theorem highPreserved (block : Fin 4) (step : Fin 8) :
    untouched (scratchHigh block) (qkSetupPc block step + 2) (queryPackGap step) := by
  fin_cases block <;> fin_cases step <;> exact ⟨by kernel_rfl,by kernel_rfl⟩

set_option maxRecDepth 100000 in
private theorem packedPreserved (block : Fin 4) (step : Fin 8) :
    untouched (9624 + step.val) (queryPackPc block step + 1)
      (qkPc block - (queryPackPc block step + 1)) := by
  fin_cases block <;> fin_cases step <;> exact ⟨by kernel_rfl,by kernel_rfl⟩

private theorem preserveReg {l : Launch} {g n r lo : Nat} {t u : TState}
    (h : untouched r lo n) (hPc : t.pc = lo) (hRun : run kernel [] l g n t = some u) :
    u.regs r = t.regs r :=
  schedulerLocalFrame (regs := [r]) (by simpa only [List.all_cons, List.all_nil, Bool.and_true]
    using h.1) h.2 hRun hPc.ge (by rw [hPc]) (by simp)

private theorem queryRegisterAfterSetup {l : Launch} {g : Nat} (block : Fin 4) (step : Fin 8)
    {lo : Nat} (hLo : lo < 2 ^ 32) (hBack : 2048 ≤ lo) (hWide : lo + 2048 < 2 ^ 32)
    {t u : TState} (ht : At t (qkPc block - 40) [])
    (hWord : t.regs (9624 + step.val) = some (b64 (lo + 2 ^ 32 * 0x40004040)))
    (hRun : run kernel [] l g 40 t = some u) :
    u.regs (9624 + step.val) =
      some (b64 (qkRetargetLow block lo + 2 ^ 32 * 0x40004040)) := by
  let first := qkPc block - 40
  let setup := qkSetupPc block step
  let before := setup - first
  let gap := queryPackGap step
  let last := queryPackPc block step + 1
  have hEnd : first + 40 = qkPc block := by fin_cases block <;> decide
  obtain ⟨hSetupLo, hSetupHi⟩ := setupPcBounds block step
  change first ≤ setup at hSetupLo
  change last ≤ qkPc block at hSetupHi
  have hLast : last = setup + 2 + gap + 1 := rfl
  have hBefore : first + before = setup := Nat.add_sub_of_le hSetupLo
  have h1 : before ≤ 40 := by omega
  have h2 : 2 ≤ 40 - before := by omega
  have h3 : gap ≤ 40 - before - 2 := by omega
  have h4 : 1 ≤ 40 - before - 2 - gap := by omega
  have hPre := inputPreserved block step
  have hLow := lowPreserved block step
  have hHigh := highPreserved block step
  have hPost := packedPreserved block step
  obtain ⟨a, ha, hRest⟩ := takeRun hRun h1
  obtain ⟨b, hb, hRest⟩ := takeRun hRest h2
  obtain ⟨c, hc, hRest⟩ := takeRun hRest h3
  obtain ⟨d, hd, hTail⟩ := takeRun hRest h4
  have hA := qkSetupLocalFrame block ht.1.ge (by have := ht.1; omega) ⟨rfl, ht.2⟩ ha
  have hAtStart : t.pc = first := ht.1
  rw [hAtStart, hBefore] at hA
  have hWordA := (preserveReg hPre ht.1 ha).trans hWord
  obtain ⟨b', hb', hB⟩ := queryUnpackAndShift block step lo a
    (hA.mono ⟨hWordA, trivial⟩)
  obtain rfl := Option.some.inj (hb.symm.trans hb')
  have hC := qkSetupLocalFrame block (by have := hB.1; omega)
    (by have := hB.1; omega) ⟨rfl, hB.2.1, hB.2.2.1, hB.2.2.2.1, trivial⟩ hc
  have hC' : At c (queryPackPc block step) (queryScratch block lo) := by
    have hL := (preserveReg hLow hB.1 hc).trans hB.2.2.2.2.1
    have hH := (preserveReg hHigh hB.1 hc).trans hB.2.2.2.2.2.1
    exact ⟨by simpa only [queryPackPc, hB.1] using hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1,
      hL, hH, trivial⟩
  obtain ⟨d', hd', hD⟩ := queryPack block step hLo hBack hWide c hC'
  obtain rfl := Option.some.inj (hd.symm.trans hd')
  have hN : 40 - before - 2 - gap - 1 = qkPc block - last := by omega
  rw [hN] at hTail
  exact (preserveReg hPost hD.1 hTail).trans hD.2.2.2.2.1

set_option maxRecDepth 10000 in
private theorem retargetWord (l : Launch) (block : Fin 4) (step : Fin 8) :
    qkRetargetLow block
      ((qStart l (otherQueryStage (qkStage block)) + qkFragment step) / 16 + 65536) =
      (qStart l (qkStage block) + qkFragment step) / 16 + 65536 := by
  have hStart : qStart l 1 = qStart l 0 + 32768 := by
    simp only [qStart, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  have hShift : ∀ addr : Nat, (addr + 32768) / 16 = addr / 16 + 2048 := by
    intro addr
    exact Nat.add_mul_div_left addr 2048 (show 0 < 16 by decide)
  have hMove : qStart l 0 + 32768 + qkFragment step =
      qStart l 0 + qkFragment step + 32768 := by omega
  by_cases h : block.val % 2 = 0
  · have hStage : qkStage block = 0 := Fin.ext h
    rw [qkRetargetLow,ite_eq_left h,hStage,show otherQueryStage 0 = 1 from rfl,hStart,hMove,hShift]
    omega
  · have hStage : qkStage block = 1 := Fin.ext (by change block.val % 2 = 1; omega)
    rw [qkRetargetLow,ite_eq_right h,hStage,show otherQueryStage 1 = 0 from rfl,hStart,hMove,hShift]

/-- Every query-bank retarget operates on the incoming Q words and preserves its Q geometry. -/
theorem retargetQkQueryBank {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (block : Fin 4) {t u : TState}
    (ht : At t (qkPc block - 40) [])
    (hWords : ∀ step : Fin 8, t.regs (9624 + step.val) =
      some (b64 (sharedDescriptorWord
        (qStart l (if qkStage block = 0 then 1 else 0) + qkFragment step) 16)))
    (hRun : run kernel [] l g 40 t = some u) :
    ∀ step : Fin 8, u.regs (9624 + step.val) =
      some (b64 (sharedDescriptorWord (qStart l (qkStage block) + qkFragment step) 16)) := by
  intro step
  let lo := (qStart l (otherQueryStage (qkStage block)) + qkFragment step) / 16 + 65536
  have hAlign := hp.shared.1
  have hBound := hp.shared.2.1
  have hStage := (otherQueryStage (qkStage block)).isLt
  have hStep := step.isLt
  have hWide : lo + 2048 < 2 ^ 32 := by dsimp [lo, qStart, qkFragment]; omega
  have hBack : 2048 ≤ lo := by dsimp [lo]; omega
  have hReg := queryRegisterAfterSetup block step (lo := lo) (by omega) hBack hWide ht
    (hWords step) hRun
  rw [retargetWord l block step] at hReg
  exact hReg

/-- The first prologue Q setup requires only the incoming Q bank. -/
theorem retargetQueryBank {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (stage : Fin 2) {t u : TState}
    (ht : At t (qkPc (initialQkBlock stage) - 40) [])
    (hWords : ∀ step : Fin 8, t.regs (9624 + step.val) =
      some (b64 (sharedDescriptorWord
        (qStart l (if stage = 0 then 1 else 0) + qkFragment step) 16)))
    (hRun : run kernel [] l g 40 t = some u) :
    ∀ step : Fin 8, u.regs (9624 + step.val) =
      some (b64 (sharedDescriptorWord (qStart l stage + qkFragment step) 16)) := by
  have hStage : qkStage (initialQkBlock stage) = stage := Fin.ext (Nat.mod_eq_of_lt stage.isLt)
  exact hStage ▸ retargetQkQueryBank hp (initialQkBlock stage) ht
    (by rw [hStage]; exact hWords) hRun

end
end PTX.Kernels.TmlFa4Fwd.Mma
