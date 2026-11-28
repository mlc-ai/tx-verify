-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Qt
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Entry
public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Lemmas.Flow.SegQCtlV
public import Lemmas.Flow.Scalars

@[expose] public section

/-! # The strict spans of the prologue: the form of the facts and the closing tactic

The value machine's facts of a state are the control table and then the data facts
(`Data.code`). The tactics read a fact list as explicit facts followed by the table, so a strict
span is stated for `dFacts`, the data facts first; `simp only [dFacts, ...]` turns the data
facts of a concrete site into explicit facts. `pro_vals` closes a computed value against the
stated one. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

/-- The value machine's facts of a state, in the form the tactics read. -/
noncomputable def dFacts (Q : Params) (L : Launch) (g : Nat) (w : Value) (d : Data.D) :
    List (Nat × Value) :=
  Data.dF Q L g d ++ facts Q L g w d.c d.c.site.pc

/-- The facts of a state's data and the control table at a program counter `pc` (a cut inside a
span). -/
noncomputable def dFactsAt (Q : Params) (L : Launch) (g : Nat) (w : Value) (d : Data.D)
    (pc : Nat) : List (Nat × Value) :=
  Data.dF Q L g d ++ facts Q L g w d.c pc

theorem mod64_32 (x : Nat) : x % 2 ^ 64 % 2 ^ 32 = x % 2 ^ 32 :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide))

theorem mod32_64 (x : Nat) : x % 2 ^ 32 % 2 ^ 64 = x % 2 ^ 32 :=
  Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by positivity)) (by decide))

theorem tb_ofInt_zero : truncBits 32 (BitVec.ofInt 64 0) = 0 := by decide

/-- A literal added to a 32-bit word. -/
theorem add_lit (x : Nat) (k : Int) (h0 : 0 ≤ k) (h1 : k < 2 ^ 31) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (x % 2 ^ 32)) + truncBits 32 (BitVec.ofInt 64 k)) =
      BitVec.ofNat 64 ((x + k.toNat) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- Close a computed register value against the stated one. -/
macro "pro_vals" : tactic => `(tactic| first
  | with_reducible rfl
  | ((try simp (disch := decide +kernel) only [valueOf_plain]) <;> first
    | with_reducible rfl
    | (simp (disch := decide +kernel) only [add_lit]; rfl)
    | (seg_close [registerValue,u32,u64,b32,b64,r32,W]; done)
    | (simp (config := {decide := true}) only [registerValue, b32, u64, b64, r32, subValue,
        Lib.word, Value.regBits, Option.getD_some, Arith32.sub32, Arith32.addi, Arith32.i32,
        Arith32.add32, Arith32.not32, Arith32.shru, Arith32.shrs, truncBits_idem, div128,
        positive, Arith32.scmpi, beq_self_eq_true, ↓reduceIte, tb_ofInt_zero]; done)
    | (simp (config := {decide := true}) only [registerValue,u32,u64,b32,b64,r32,W, DType.width,
        truncBits,
        BitVec.toNat_ofNat, subValue, Lib.word, Arith32.sub32, Value.regBits, Option.getD_some,
        BitVec.toNat_sub, Arith32.addi, Arith32.i32, Arith32.add32, Arith32.not32,
        BitVec.toNat_not, BitVec.toNat_add, BitVec.toNat_ofInt, truncBits_idem, mod64_32,
        mod32_64, div128, Arith32.shru, Arith32.shrs, positive, Arith32.scmpi, beq_self_eq_true,
        ↓reduceIte, Nat.mod_mod, qTok, qRow, queryReg, queryValue, Nat.reduceSub, Nat.reduceMul,
        Nat.add_zero]
       first
         | done
         | (congr 2; omega)
         | (generalize _ % Launch.block _ = tid; congr 2; omega))
    | rfl)
  | rfl)

/-- Normalize the data facts of a concrete state to explicit facts. -/
macro "pro_facts" : tactic => `(tactic| simp only [dFacts, dFactsAt, Data.dF, Data.tags, Data.pos,
  Data.early, Data.oldTags, Data.qTags, Data.qhs, List.map_cons, List.map_nil, List.cons_append,
  List.nil_append, Data.Tag.reg, Data.Tag.val, ↓reduceIte, Site.pc, Data.rowVal, Data.colVal,
  List.getD_cons_zero,
  List.getD_cons_succ, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd, Nat.reduceMul,
  elPc, initPc, Bool.false_eq_true, List.append_nil])

/-- A strict span between the facts in the tactics' form (after the facts `pre` of a load) is one
between the machine's facts. -/
theorem dFacts_seg {Q : Params} {L : Launch} {g : Nat} {w : Value} {qt : Nat → Env}
    {a b : Nat} {d dn : Data.D} {pre : List (Nat × Value)}
    (h : SegQ kernel Assumptions.all L g (QT qt) a (pre ++ dFacts Q L g w d) b
      (dFacts Q L g w dn)) :
    SegQ kernel Assumptions.all L g (QT qt) a (pre ++ (Data.code Q L g w).facts d) b
      ((Data.code Q L g w).facts dn) := by
  intro t ht hq
  obtain ⟨hp, hs, ha, hf, hr⟩ := ht
  obtain ⟨u, hr', ⟨p1, p2, p3, p4, p5⟩, hQ⟩ := h t ⟨hp, hs, ha, hf, by
    simpa [dFacts, Data.code, holds_append, and_comm, and_left_comm] using hr⟩ hq
  exact ⟨u, hr', ⟨p1, p2, p3, p4, by simpa [dFacts, Data.code, and_comm] using p5⟩, hQ⟩

/-- A strict span of the prologue between facts in the form of `dFacts`/`dFactsAt`. -/
macro "pro_seg" : tactic => `(tactic| (pro_facts; segq_ctlt proQt,
    (plainRules_pro (a := 27) (b := 574) le_rfl),
    (plainSegs_pro (a := 27) (b := 574) le_rfl), Lib.rulesFrame using pro_vals))

/-- **The first segment**: from the setmaxnreg to the first request load. -/
theorem sMax_span {Q : Params} {L : Launch} {g : Nat} {w : Value} (won : Bool) (bcast : Value)
    (v : Data.Vals) :
    let d : Data.D := ⟨⟨.sMax, b32 0, b32 0, b32 0, won, bcast⟩, v⟩
    let dn : Data.D := ⟨⟨.ld 0, b32 0, b32 0, b32 0, won, bcast⟩, v⟩
    SegQ kernel Assumptions.all L g (QT proQt) 28 (dFacts Q L g w d) 34 (dFacts Q L g w dn) := by
  intro d dn
  simp only [d, dn]
  pro_seg

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
