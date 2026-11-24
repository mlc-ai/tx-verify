-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTotG
public import Lemmas.Flow.FmaTotal
public import Lemmas.Flow.FloatDat
public import Lemmas.Flow.SetpCore

@[expose] public section

/-! # The words after the stage on any words

The state after the shuffle of the row maximum on any words (`D.afterMaxT`) has the words the
loop's tail needs (`Sm.NumInv`): `alpha` is an `.f32` datum (`f32Dat_alT`), the new maximum a
four-byte word (`mnT_bytes`), and the 24 packed pairs of probabilities have conversions to
`bf16` (`pqOk_afterMaxT`). The last holds because every packed pair is an operand of an
`add.f32x2` of the sum tree, which has no rounding modifier and therefore no Core rule: where it
has an outcome, the ideal rule read both of its operands as two extended reals
(`add2NE_ok_read`), and the conversion of two extended reals has an outcome. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-! ### `alpha` and the new maximum -/

theorem f32Dat_okVal {E : Exec Value} (h : ∀ v, E = .ok v → F32Dat v) :
    F32Dat (okVal (b32 0) E) := by
  rcases hE : E with e | v
  · exact f32Dat_bits _
  · exact h v hE

theorem f32Dat_alT (d : D) (recv : Value) : F32Dat (d.alT recv) := by
  show F32Dat (okVal (b32 0) (d.t8E recv))
  refine f32Dat_okVal fun v hv => ?_
  unfold D.t8E at hv
  rw [movE_eq hv]
  split
  · exact f32Dat_bits _
  · exact f32Dat_okVal fun w hw => ex2E_dat hw

theorem f32Dat_bytes {v : Value} (h : F32Dat v) : v.bytes = 4 := by
  obtain ⟨c, hc⟩ := h
  exact classify_f32_bytes hc

theorem mnT_bytes (d : D) (recv : Value) : (d.mnT recv).bytes = 4 := by
  show (okVal (b32 0) (d.t1E recv)).bytes = 4
  exact f32Dat_bytes (f32Dat_okVal fun v hv => maxE_dat hv)

/-! ### `add.f32x2` without a rounding modifier reads its operands -/

theorem lane_add2NI (xs : List FVal) : FloatInstr.lane add2NI xs = none := by
  simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.arith]

theorem coreFloat_add2NI (va vb : Value) : (coreFloat add2NI [va, vb]).toBool = false := by
  unfold coreFloat
  have h2 : List.range add2NI.ty.lanes = [0, 1] := rfl
  rw [h2]
  simp only [List.mapM_cons, List.mapM_nil, lane_add2NI, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw]
  rcases hA : classify FloatFmt.f32 (floatLane { fmt := FloatFmt.f32, lanes := 2 } va 0) with
    e | x <;>
  rcases hB : classify FloatFmt.f32 (floatLane { fmt := FloatFmt.f32, lanes := 2 } vb 0) with
    e' | y <;>
  simp [Except.toBool]

theorem add2NE_ok_read {va vb : Value} (h : (add2NE va vb).toBool = true) :
    (∃ p, pairRead va = some (.ok p)) ∧ ∃ p, pairRead vb = some (.ok p) := by
  unfold add2NE at h
  cases hi : idealAdd2 va vb with
  | none =>
    rw [hi] at h
    simp only at h
    rw [coreFloat_add2NI] at h
    cases h
  | some r =>
    rw [hi] at h
    unfold idealAdd2 at hi
    rcases hA : pairRead va with _ | (e | ⟨x0, x1⟩)
    · simp [hA, bindRead] at hi
    · simp only [hA, bindRead, Option.some.injEq] at hi
      subst hi
      simp [Except.toBool] at h
    rcases hB : pairRead vb with _ | (e | ⟨y0, y1⟩)
    · simp [hA, hB, bindRead] at hi
    · simp only [hA, hB, bindRead, Option.some.injEq] at hi
      subst hi
      simp [Except.toBool] at h
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem pairRead_halves {v : Value} {p : EReal × EReal} (h : pairRead v = some (.ok p)) :
    (∃ x, readEReal .f32 (splitValue 64 v).1 = some (.ok x)) ∧
      ∃ y, readEReal .f32 (splitValue 64 v).2 = some (.ok y) := by
  unfold pairRead at h
  split at h <;> simp_all

theorem join8 {a b : Value} (ha : a.bytes = 4) (hb : b.bytes = 4) :
    (joinValue a b).bytes = 8 := by
  unfold joinValue
  split
  · split_ifs with h
    · obtain ⟨-, -, h3⟩ := h
      simp only [Value.bytes] at ha hb
      omega
    · simp only [Value.bytes] at ha hb ⊢
      omega
  · split_ifs with h
    · simp only [Value.bytes] at ha hb ⊢
      omega
    · simp only [Value.bytes] at ha hb ⊢
      omega
  · simp only [Value.bytes] at ha hb ⊢
    omega

/-! ### The packed pairs are read by the sum tree -/

/-- The first instruction of the sum tree that reads the pair `%rd(46 + q)`. -/
def useIdx (q : Nat) : Nat :=
  ((List.range 63).find? fun c => match (psCode[c]? : Option PI) with
    | some (PI.ad _ a b) => a == 1994 + q || b == 1994 + q
    | _ => false).getD 0

/-- The instruction `useIdx q` adds the pair, and the pair's last write before it is its pack. -/
def useChk (q : Nat) : Bool :=
  decide (useIdx q < 63) &&
  (match psCode[useIdx q]? with
    | some (.ad _ a b) => a == 1994 + q || b == 1994 + q
    | _ => false) &&
  (match (psCode.take (useIdx q)).reverse.find? (fun i => i.dst == 1994 + q) with
    | some (.pk d a b) => d == 1994 + q && a == 1287 + 2 * (2 * pairW q) &&
        b == 1287 + 2 * (2 * pairW q + 1)
    | _ => false)

theorem useChk_all : ∀ q < 24, useChk q = true := by decide +kernel

theorem pairW_mod : ∀ q < 24, pairW q % 8 < 6 := by decide +kernel

theorem psV63_pair (d : D) (recv : Value) {q : Nat} (hq : q < 24) :
    lkV (psV (sgT L g d recv) 63) (1994 + q) =
      joinValue (d.pvT L g recv (2 * pairW q)) (d.pvT L g recv (2 * pairW q + 1)) := by
  have h := xtT_pair d recv (fun _ => b32 0) (L := L) (g := g) hq
  simp only [xtT, xt1T] at h
  rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
    valueEx_cons_ne _ _ (by omega)] at h
  unfold valueEx at h
  rw [lookup_append_some (psV_pair (sgT L g d recv) hq), Option.getD_some] at h
  unfold lkV
  rw [psV_pair (sgT L g d recv) hq, Option.getD_some]
  exact h

/-- **The pair `%rd(46 + q)` reads as two extended reals** where the sum tree has outcomes. -/
theorem pair_read (d : D) (recv : Value) (hps : PsOk (sgT L g d recv) 63) {q : Nat}
    (hq : q < 24) :
    ∃ p, pairRead (joinValue (d.pvT L g recv (2 * pairW q))
      (d.pvT L g recv (2 * pairW q + 1))) = some (.ok p) := by
  have hc := useChk_all q hq
  unfold useChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hlt, hadd⟩, hpk⟩ := hc
  set c := useIdx q
  set sg := sgT L g d recv
  have hlk : lkV (psV sg c) (1994 + q) = lkV (psV sg 63) (1994 + q) := by
    split at hpk
    · rename_i dd a b hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hpk
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpk
      unfold lkV
      rw [psV_pair sg hq]
      unfold psV
      rw [lookup_fold_pk sg (psCode.take c) [] hf]
    · cases hpk
  rw [← psV63_pair d recv hq, ← hlk]
  split at hadd
  · rename_i dd a b hi
    have hok := hps c hlt _ hi
    simp only [PI.okV] at hok
    obtain ⟨h1, h2⟩ := add2NE_ok_read hok
    simp only [Bool.or_eq_true, beq_iff_eq] at hadd
    rcases hadd with rfl | rfl
    · exact h1
    · exact h2
  · cases hadd

/-- **The 24 packed pairs have conversions** after the stage on any words, where no instruction
of the stage faults. -/
theorem pqOk_afterMaxT {d : D} {recv : Value} (hok : d.s2Ok L g recv) :
    (d.afterMaxT L g recv).pqOk := by
  intro q hq
  obtain ⟨p, hp⟩ := pair_read d recv hok.2.2.2.2.2.1 hq
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := pairRead_halves hp
  have hb8 := join8 (pvT_bytes (L := L) (g := g) d recv (2 * pairW q))
    (pvT_bytes (L := L) (g := g) d recv (2 * pairW q + 1))
  have hu : unpackE 64 (joinValue (d.pvT L g recv (2 * pairW q))
      (d.pvT L g recv (2 * pairW q + 1))) = .ok (splitValue 64 (joinValue
        (d.pvT L g recv (2 * pairW q)) (d.pvT L g recv (2 * pairW q + 1)))) := by
    unfold unpackE
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hb8, readEReal_f32_bytes hx, readEReal_f32_bytes hy⟩)]
  simp only [D.pwE, D.afterMaxT, pairW_mod q hq, ite_true]
  rw [hu]
  simp only [Except.bind, cvtBfE, hx, hy, Except.toBool]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
