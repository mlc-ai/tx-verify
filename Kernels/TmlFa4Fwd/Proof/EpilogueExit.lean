-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanGuard
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.WarpScan
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem branch {l : Launch} {g : Nat} {t : TState} {r dst : Nat} {take : Bool}
    (hf : t.fault = none) (hc : kernel.code[t.pc]? = some ⟨some (r, false), .bra dst false⟩)
    (hr : t.regs r = some (.pred take)) :
    tauStep kernel [] l g t = some (if take then {t with pc := dst} else skip t) := by
  cases take <;>
    simp [tauStep, out, hf, hc, guardHolds, readReg, hr, Op.isLocal, execLocalA,
      execLocalRule, execLocal, Op.rule, execBranch, bind, Except.bind, pure, Except.pure]

private theorem localStep {l : Launch} {g : Nat} {t u : TState} {op : Op}
    (hf : t.fault = none) (hc : kernel.code[t.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (he : execLocal l g t op = .ok u) :
    tauStep kernel [] l g t = some u := by
  have he' : execLocalA [] l g t op = .ok u := he
  simp only [tauStep, out, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, he']

/-- The scheduler repeats the cuQ scan after the second O buffer has been released. -/
theorem drainScanBranch {p : Params} {l : Launch} {g : Nat} {t : TState}
    (hpc : t.pc = 2986) (hf : t.fault = none)
    (hr : t.regs 307 = some (.pred (p.batch < laneOf l g))) :
    tauStep kernel [] l g t =
      some (if p.batch < laneOf l g then {t with pc := 2990} else skip t) := by
  have h := branch (l := l) (g := g) hf (by rw [hpc]; exact Flow.code_2986) hr
  split <;> simp_all

/-- The first lane lookup in the drain scan reads the same cuQ array as the entry scan. -/
theorem drainLaneRead {p : Params} {l : Launch} {m : Mem0} {A : List Assumption} (hp : Pre p l m)
    (g : Nat) (t : TState) (hLane : laneOf l g ≤ p.batch)
    (hModel : ∀ {s : TState}, 2987 ≤ s.pc → s.pc ≤ 2989 →
      out kernel A l g s = out kernel [] l g s)
    (hpc : t.pc = 2987) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hIndex : t.regs 1201 = some (.bits 32 (BitVec.ofNat 64 (laneOf l g))))
    (hBase : t.regs 7506 = some (b64 p.cuQBase)) :
    ∃ u, run kernel A l g 2 t = some u ∧ u.pc = 2989 ∧ u.fault = none ∧
      u.sub = 0 ∧ u.acc = [] ∧
      (∀ r, r ≠ 7872 → r ≠ 7873 → u.regs r = t.regs r) ∧
      out kernel A l g u = .ev (.read
        { loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4 } (afterLoad u [7229])) := by
  let lane := laneOf l g
  let t1 := next (setReg t 7872 (b64 (4 * lane)))
  let t2 := next (setReg t1 7873 (b64 (p.cuQBase + 4 * lane)))
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  have hOff : 4 * lane < 2 ^ 64 := by omega
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hB : p.cuQBase < 2 ^ 64 := by omega
  have hSum : p.cuQBase + 4 * lane < 2 ^ 64 := by change lane ≤ p.batch at hLane; omega
  have h1 : tauStep kernel [] l g t = some t1 := by
    apply localStep hf (by rw [hpc]; exact Flow.code_2987) rfl
    rw [execLocal_int rfl]
    change t.regs 1201 = some (.bits 32 (BitVec.ofNat 64 lane)) at hIndex
    simp only [execInt, DType.width, DType.kind?, readBits, readReg, hIndex, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat h32 (by decide)]
    change Except.ok (next (setReg t 7872
      (b64 ((BitVec.ofNat 64 lane).toNat * 4)))) = .ok t1
    rw [toNat_ofNat_lt h64, Nat.mul_comm lane 4]
  have hp1 : t1.pc = 2988 := by change t.pc + 1 = 2988; rw [hpc]
  have h2 : tauStep kernel [] l g t1 = some t2 := by
    have hb : t1.regs 7506 = some (b64 p.cuQBase) := by simpa [t1, next, setReg] using hBase
    have ho : t1.regs 7872 = some (b64 (4 * lane)) := by simp [t1, next, setReg]
    apply localStep (t := t1) hf (by rw [hp1]; exact Flow.code_2988) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, b64, readValue, readBits, readReg, hb, ho, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hB (by decide), truncBits_ofNat hOff (by decide),
      ← BitVec.ofNat_add, truncBits_ofNat hSum (by decide), t2]
  have hp2 : t2.pc = 2989 := by change t.pc + 1 + 1 = 2989; rw [hpc]
  refine ⟨t2, ?_, hp2, hf, hs, ha, ?_, ?_⟩
  · have hA1 : tauStep kernel A l g t = some t1 := by
      rw [tauStep, hModel (by omega) (by omega), ← tauStep]
      exact h1
    have hA2 : tauStep kernel A l g t1 = some t2 := by
      rw [tauStep, hModel (by omega) (by omega), ← tauStep]
      exact h2
    simp only [run, hA1, hA2, Option.bind_some]
  · intro r h₂ h₃
    simp [t2, t1, next, setReg, h₂, h₃]
  · rw [hModel (by omega) (by omega)]
    have hr : t2.regs 7873 = some (b64 (p.cuQBase + 4 * lane)) := by simp [t2, next, setReg]
    have hal := hp.alignment.2.2.2.2.2.2.2.2.1
    rw [out_event (t := t2) hf (by rw [hp2]; exact Flow.code_2989) rfl rfl]
    change Out.ev (loadTmpl [] l g t2 .global false 32 [7229] 7873 0) = _
    exact congrArg Out.ev (loadTmpl_global (t := t2) (w := 32) hs hr hSum (by decide) (by omega))

/-- Every lane starts the drain scan with a down shuffle, including lanes past the sentinel. -/
theorem drainFirstShuffle {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (cuq : Nat) (hpc : t.pc = 2990) (hf : t.fault = none)
    (hv : t.regs 7229 = some (.bits 32 (BitVec.ofNat 64 cuq))) :
    out kernel [] l g t = .ev (.shfl .down (.bits 32 (BitVec.ofNat 64 cuq)) 1 31
      (fun value _ => next (setReg t 2401 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2990) rfl rfl]
  change Out.ev (shflTmpl l g t .down 2401 none (.reg 7229) (.imm 1) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, readBits, pure, Except.pure]
  rfl

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- The final group exits directly when all batches were skipped. A selected group instead
reaches the final ballot sequence. -/
theorem drainGroupExit {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (first : Nat) (hpc : t.pc = 3086) (hf : t.fault = none)
    (hFirst : first ≤ p.batch) (ha : t.regs 7235 = some (b32 first))
    (hb : t.regs 7147 = some (b32 p.batch)) :
    ∃ u, run kernel [] l g 2 t = some u ∧ u.fault = none ∧
      u.pc = (if first = p.batch then 3099 else 3088) ∧
      ∀ r ≠ 331, u.regs r = t.regs r := by
  let v := next (setReg t 331 (.pred (p.batch ≤ first)))
  let u := if p.batch ≤ first then {v with pc := 3099} else skip v
  have hBatch := hp.shape.2.1
  have hF : first < 2 ^ 31 := by omega
  have h1 : tauStep kernel [] l g t = some v := by
    apply localStep hf (by rw [hpc]; exact Flow.code_3086) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, DType.kind?, b32, readBits, readReg, ha, hb,
      bind, Except.bind, pure, Except.pure, truncBits_ofNat (show first < 2 ^ 32 by omega)
        (by decide), truncBits_ofNat (show p.batch < 2 ^ 32 by omega) (by decide)]
    change (Except.ok (next (setReg t 331 (.pred (decide
      (toSigned 32 (BitVec.ofNat 64 p.batch) ≤ toSigned 32 (BitVec.ofNat 64 first)))))) :
        Exec TState) = .ok v
    simp only [signedWord hF, signedWord hBatch, Int.ofNat_le, v]
  have hv : v.pc = 3087 := by change t.pc + 1 = 3087; rw [hpc]
  have h2 : tauStep kernel [] l g v = some u := by
    have hr : v.regs 331 = some (.pred (p.batch ≤ first)) := by simp [v, next, setReg]
    have h := branch (l := l) (g := g) (t := v) hf (by rw [hv]; exact Flow.code_3087) hr
    by_cases h' : p.batch ≤ first <;> simpa [u, h'] using h
  refine ⟨u, by simp only [run, h1, h2, Option.bind_some], ?_, ?_, ?_⟩
  · unfold u
    split <;> exact hf
  · by_cases h : first = p.batch
    · simp [u, h]
    · have hn : ¬p.batch ≤ first := by omega
      simp [u, h, hn, skip, v, next, setReg, hpc]
  · intro r hr
    by_cases h : p.batch ≤ first <;> simp [u, h, skip, v, next, setReg, hr]

/-- The two copies of the prefix fold during the drain scan use the same lane inputs. -/
def drainScanPc (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 3066 else 3009) + 3 * stage.val

def drainScanSrc (later : Bool) (stage : Fin 5) : Nat :=
  if stage.val = 0 then 7232 else (if later then 2428 else 2407) + 3 * stage.val

def drainScanDst (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 2429 else 2408) + 3 * stage.val

def drainScanSum (later : Bool) (stage : Fin 5) : Nat :=
  if stage.val = 4 then 7233 else drainScanDst later stage + 2

def drainScanGuardReg (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 329 else 315) - stage.val

/-- The two drain-scan loops set the five lane predicates before the first shuffle. -/
theorem drainScanPrepare (later : Bool) (l : Launch) (g : Nat) {lane : Nat}
    (hl : lane < 32) :
    Seg kernel [] l g 5 (drainScanPc later 0 - 5) [(1201, b32 lane)]
      (drainScanPc later 0)
      [(drainScanGuardReg later 4, .pred (drainScanGuard 4 lane)),
       (drainScanGuardReg later 3, .pred (drainScanGuard 3 lane)),
       (drainScanGuardReg later 2, .pred (drainScanGuard 2 lane)),
       (drainScanGuardReg later 1, .pred (drainScanGuard 1 lane)),
       (drainScanGuardReg later 0, .pred (drainScanGuard 0 lane))] := by
  have hLane : lane < 2 ^ 32 := by omega
  have hLane64 : lane < 2 ^ 64 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  have hG0 : drainScanGuard 0 lane = decide (lane = 0) := rfl
  have hG1 : drainScanGuard 1 lane = decide (2 ≤ lane) := rfl
  have hG2 : drainScanGuard 2 lane = decide (4 ≤ lane) := rfl
  have hG3 : drainScanGuard 3 lane = decide (8 ≤ lane) := rfl
  have hG4 : drainScanGuard 4 lane = decide (16 ≤ lane) := rfl
  cases later <;>
    intro t ht <;>
    seg_fp ht using
      (simp only [hG0, hG1, hG2, hG3, hG4, compare, Option.getD_some,
         truncBits_ofNat hLane (by decide), toNat_ofNat_lt hLane64,
         Value.pred.injEq, decide_eq_decide, hz, h1, h3, h7, h15]
       all_goals omega)

theorem drainScanCode (later : Bool) (stage : Fin 5) :
    kernel.code[drainScanPc later stage]? =
      some ⟨none, .warp ⟨.shfl .up, some (.int .b 32), [some (drainScanDst later stage)],
        [.reg (drainScanSrc later stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0],
        some (.imm (-1))⟩⟩ := by
  cases later <;> fin_cases stage
  · exact Flow.code_3009
  · exact Flow.code_3012
  · exact Flow.code_3015
  · exact Flow.code_3018
  · exact Flow.code_3021
  · exact Flow.code_3066
  · exact Flow.code_3069
  · exact Flow.code_3072
  · exact Flow.code_3075
  · exact Flow.code_3078

theorem drainScanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (later : Bool) (stage : Fin 5) (g : Nat) (t : TState) (value : Nat)
    (hpc : t.pc = drainScanPc later stage) (hf : t.fault = none)
    (hv : t.regs (drainScanSrc later stage) = some (b32 value)) :
    out kernel [] l g t = .ev (.shfl .up (b32 value) (2 ^ stage.val) 0
      (fun val _ => next (setReg t (drainScanDst later stage) val))) := by
  have hc := drainScanCode later stage
  rw [← hpc] at hc
  rw [out_event hf hc rfl rfl]
  change Out.ev (shflTmpl l g t .up (drainScanDst later stage) none
    (.reg (drainScanSrc later stage)) (.imm ((2 ^ stage.val : Nat) : Int))
    (.imm 0) (.imm (-1))) = _
  have hWidth : 2 ^ stage.val < 2 ^ 32 :=
    Nat.pow_lt_pow_right (by decide) (by have := stage.isLt; omega)
  have hBits : readBits l g t 32 (.imm ((2 ^ stage.val : Nat) : Int)) =
      .ok (BitVec.ofNat 64 (2 ^ stage.val)) := by
    simp only [readBits, BitVec.ofInt_natCast, truncBits_ofNat hWidth (by decide),
      pure, Except.pure]
  have hb : l.block % 32 = 0 := by rw [hp.block]
  have hm : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hz : readBits l g t 32 (.imm 0) = .ok 0 := rfl
  simp only [shflTmpl, readValue, readReg, hv, hb, hBits, hm, hz, pure, Except.pure,
    toNat_ofNat_lt (show 2 ^ stage.val < 2 ^ 64 by omega)]
  rfl

theorem drainScanCombine (later : Bool) (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (drainScanPc later stage + 1)
      [(drainScanGuardReg later stage, .pred (drainScanGuard stage lane)),
       (drainScanSrc later stage, b32 left), (drainScanDst later stage, b32 recv)]
      (drainScanPc later stage + 3)
      [(drainScanSum later stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  have hLeft : left < 2 ^ 32 := by omega
  have hRecv : recv < 2 ^ 32 := by omega
  by_cases h : 2 ^ stage.val ≤ lane
  · have hp : drainScanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [drainScanGuard, hst, show lane ≠ 0 by omega]
      · simp [drainScanGuard, h, hst]
    cases later <;> fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;> seg_fp ht using norm_bits [ite_eq_left h]
  · have hp : drainScanGuard stage lane = decide (stage.val = 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [drainScanGuard, hst, show lane = 0 by omega]
      · simp [drainScanGuard, h, hst]
    cases later <;> fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;> seg_fp ht using norm_bits [ite_eq_right h]

theorem drainScanFold (later : Bool) (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hl : lane < 32)
    (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 2 (drainScanPc later stage + 1)
      [(drainScanGuardReg later stage, .pred (drainScanGuard stage lane)),
      (drainScanSrc later stage, b32 (prefixWindow xs (2 ^ stage.val) lane)),
      (drainScanDst later stage,
        b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (drainScanPc later stage + 3)
      [(drainScanSum later stage, b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := drainScanCombine later stage l g hl hsum
  have hoff : 2 ^ stage.val < 32 := Nat.pow_lt_pow_right (by decide) stage.isLt
  rw [shflSource_up hoff] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

/-- The final drain ballot compares each lane's request end with the CTA index. -/
theorem drainBallotArgs (l : Launch) (g : Nat) {base count lanePrefix heads cta : Nat}
    (hPrefix : lanePrefix ≤ count) (hCount : count < 2 ^ 31) (hHead : heads < 2 ^ 31)
    (hCTA : cta < 2 ^ 31) (hEnd : base + count * heads < 2 ^ 31) :
    Seg kernel [] l g 4 3088
      [(7234, b32 count), (7138, b32 heads), (7236, b32 (base + count * heads)),
       (7233, b32 lanePrefix), (1072, b32 cta)] 3092
      [(332, .pred (decide (base + lanePrefix * heads ≤ cta)))] := by
  have hPH := Nat.mul_le_mul_right heads hPrefix
  have hBase : base < 2 ^ 31 := by omega
  have hProd : count * heads < 2 ^ 31 := by omega
  have hPre : lanePrefix < 2 ^ 31 := by omega
  have hPE : base + lanePrefix * heads < 2 ^ 31 := by omega
  intro t ht
  seg_fp ht using
    first
    | norm_cmp
    | (simp only [compare, Option.getD_some, ← BitVec.ofNat_mul,
        truncBits_ofNat (show count < 2 ^ 32 by omega) (by decide),
        truncBits_ofNat (show heads < 2 ^ 32 by omega) (by decide),
        truncBits_ofNat (show lanePrefix < 2 ^ 32 by omega) (by decide),
        truncBits_ofNat (show cta < 2 ^ 32 by omega) (by decide)]
       norm_cmp)

/-- The tail ballot supplies the first lane in the group whose end is above the CTA index. -/
theorem drainBallotTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (pred : Bool) (hpc : t.pc = 3092) (hf : t.fault = none)
    (hpredict : t.regs 332 = some (.pred pred)) :
    out kernel [] l g t =
      .ev (.vote (2 ^ 32 - 1) pred (fun value => next (setReg t 2446 (b32 value.toNat)))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_3092) rfl rfl]
  change Out.ev (voteTmpl l g t 2446 332 false (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [voteTmpl, readPred, readReg, hpredict, hb, b32, readBits, pure, Except.pure]
  rfl

/-- The trailing ballot count selects the first request whose prefix exceeds the CTA index. -/
theorem drainBallotCount (l : Launch) (g : Nat) (word : BitVec 32) {n : Nat}
    (hn : n ≤ 32) (hBits : ∀ lane < 32, word.getLsbD lane = decide (lane < n)) :
    Seg kernel [] l g 2 3093 [(2446, b32 word.toNat)] 3095
      [(1214, b32 n), (333, .pred (decide (word.toNat = 0)))] := by
  intro t ht
  have hw32 := word.isLt
  have hw64 : word.toNat < 2 ^ 64 := by omega
  have hPop := ballot_popc_prefix hn hBits
  have hz : (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 := rfl
  seg_fp ht using
    (simp only [Value.pred.injEq, compare, b32, Option.getD_some,
      truncBits_ofNat hw32 (by decide), toNat_ofNat_lt hw64, hz, hPop,
      decide_eq_decide]
     all_goals omega)

/-- Empty ballots skip the first indexed shuffle. A nonempty ballot first reads the preceding
lane and then the selected one. -/
theorem drainBallotBranch (l : Launch) (g : Nat) (t : TState) (take : Bool)
    (hpc : t.pc = 3095) (hf : t.fault = none) (ht : t.regs 333 = some (.pred take)) :
    tauStep kernel [] l g t = some (if take then {t with pc := 3098} else skip t) :=
  branch hf (by rw [hpc]; exact Flow.code_3095) ht

theorem drainPreviousLane (l : Launch) (g : Nat) {n : Nat} (hn : 0 < n) (hN : n < 32) :
    Seg kernel [] l g 1 3096 [(1214, b32 n)] 3097 [(2447, b32 (n - 1))] := by
  intro t ht
  seg_fp ht using norm_bits

theorem drainTailShuffleCode (previous : Bool) :
    kernel.code[if previous then 3097 else 3098]? =
      some ⟨none, .warp ⟨.shfl .idx, some (.int .b 32),
        [some (if previous then 2448 else 2449)],
        [.reg (if previous then 7233 else 7232), .reg (if previous then 2447 else 1214), .imm 31],
        some (.imm (-1))⟩⟩ := by
  cases previous
  · exact Flow.code_3098
  · exact Flow.code_3097

theorem drainTailShuffle {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (previous : Bool) (g : Nat) (t : TState) (value lane : Nat) (hLane : lane < 32)
    (hpc : t.pc = (if previous then 3097 else 3098)) (hf : t.fault = none)
    (hs : t.regs (if previous then 7233 else 7232) = some (b32 value))
    (hl : t.regs (if previous then 2447 else 1214) = some (b32 lane)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 value) lane 31
      (fun val _ => next (setReg t (if previous then 2448 else 2449) val))) := by
  rw [out_event hf (by rw [hpc]; exact drainTailShuffleCode previous) rfl rfl]
  change Out.ev (shflTmpl l g t .idx (if previous then 2448 else 2449) none
    (.reg (if previous then 7233 else 7232)) (.reg (if previous then 2447 else 1214))
    (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  simp only [shflTmpl, readValue, readReg, hs, hl, hb, b32, readBits,
    bind, Except.bind, truncBits_ofNat h32 (by decide), toNat_ofNat_lt h64, pure, Except.pure]
  rfl

/-- Immediately after the final index shuffle, the accepted event resumes at the kernel exit
branch and all remaining steps are local. -/
theorem drainAfterTailShuffle (l : Launch) (g : Nat) (t u : TState) (event : Event)
    (value lane : Nat) (hpc : t.pc = 3098) (hf : t.fault = none)
    (hw : t.regs 1062 = some (.bits 32 13))
    (hFire : Fires t.pc (.shfl .idx (b32 value) lane 31
      (fun v _ => next (setReg t 2449 v))) event (some u)) :
    ∃ v, run kernel [] l g 5 u = some v ∧ v.pc = Flow.exit_0 ∧ out kernel [] l g v = .ev .exit := by
  obtain ⟨recv, ok, -, hh⟩ := hFire
  obtain rfl := Option.some.inj hh
  have hp : (next (setReg t 2449 recv)).pc = 3099 := by
    change t.pc + 1 = 3099
    rw [hpc]
  exact finishScheduler l g _ hp hf (by simpa [next, setReg] using hw)

end

end PTX.Kernels.TmlFa4Fwd.Epilogue
