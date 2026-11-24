-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Widen

@[expose] public section

/-! # Runs of packs, then runs of packed multiplications

A proof tool, for code that first packs pairs of loaded 32-bit words (`mov.b64 d, {a, b}`) and
then multiplies the packed pairs elementwise by one pair `c` (`mul.f32x2 d', d, c`), as a
Tensor Memory rescale does. The words are raw values (a load may return anything):

* `packs_run`: a run of packs whose sources hold `v` and whose destinations are no source.
  When every source word has four bytes (`packsOk`), local steps write each destination with the
  joined pair (`packRun`); otherwise the thread is dead.
* `muls_run`: a run of packed multiplications, under the ideal reading of `mul.f32x2` at each of
  its states. When the four elements of every source pair and of `c` read as `f32` operands
  (`mulsOk`), local steps write each destination with the pair of products (`mulVal`);
  otherwise the thread is dead.

`pairOk` and `pairMul` (`Widen`) are a pack followed by a multiplication (`pairOk_eq`,
`pairMul_eq`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-! ### Packs -/

/-- The packs `(d, a, b)` (`mov.b64 d, {a, b}`) from `pc` on. -/
def PackCode (K : Kernel) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | pc, p :: ps =>
    K.code[pc]? =
        some ⟨none, .move ⟨.pack, .int .b 64, [some p.1], [.reg p.2.1, .reg p.2.2]⟩⟩ ∧
      PackCode K (pc + 1) ps

/-- `PackCode` decided on the code. -/
def packCodeB (K : Kernel) : Nat → List (Nat × Nat × Nat) → Bool
  | _, [] => true
  | pc, p :: ps =>
    (match K.code[pc]? with
      | some ⟨none, .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩⟩ =>
        d == p.1 && a == p.2.1 && b == p.2.2
      | _ => false) && packCodeB K (pc + 1) ps

theorem PackCode.of_bool : ∀ {pc : Nat} {ps : List (Nat × Nat × Nat)},
    packCodeB K pc ps = true → PackCode K pc ps
  | _, [], _ => trivial
  | pc, p :: ps, h => by
    simp only [packCodeB, Bool.and_eq_true] at h
    refine ⟨?_, PackCode.of_bool h.2⟩
    have h1 := h.1
    split at h1
    · rename_i d a b hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      rw [hc, h1.1.1, h1.1.2, h1.2]
    · cases h1

/-- Every source word of the packs has four bytes. -/
def packsOk (v : Nat → Value) (ps : List (Nat × Nat × Nat)) : Bool :=
  ps.all fun p => (v p.2.1).bytes == 4 && (v p.2.2).bytes == 4

/-- The state after the packs, from source values `v`. -/
def packRun (v : Nat → Value) : TState → List (Nat × Nat × Nat) → TState
  | t, [] => t
  | t, p :: ps => packRun v (PTX.next (setReg t p.1 (joinValue (v p.2.1) (v p.2.2)))) ps

theorem packRun_skel (v : Nat → Value) : ∀ (ps : List (Nat × Nat × Nat)) (t : TState),
    (packRun v t ps).pc = t.pc + ps.length ∧ (packRun v t ps).sub = t.sub ∧
      (packRun v t ps).acc = t.acc ∧ (packRun v t ps).fault = t.fault
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | p :: ps, t => by
    obtain ⟨h1, h2, h3, h4⟩ := packRun_skel v ps (PTX.next (setReg t p.1
      (joinValue (v p.2.1) (v p.2.2))))
    refine ⟨?_, h2, h3, h4⟩
    rw [packRun, h1]
    simp only [PTX.next, setReg, List.length_cons]
    omega

/-- A register no pack writes keeps its value. -/
theorem packRun_other (v : Nat → Value) {r : Nat} : ∀ (ps : List (Nat × Nat × Nat)) (t : TState),
    (∀ p ∈ ps, p.1 ≠ r) → (packRun v t ps).regs r = t.regs r
  | [], _, _ => rfl
  | p :: ps, t, h => by
    rw [packRun, packRun_other v ps _ (fun q hq => h q (by simp [hq]))]
    simp [PTX.next, setReg, Function.update_of_ne (h p (by simp)).symm]

/-- The destination of a pack holds the joined pair, when no other pack writes it. -/
theorem packRun_val (v : Nat → Value) {d a b : Nat} : ∀ (ps : List (Nat × Nat × Nat))
    (t : TState), (ps.map Prod.fst).Nodup → (d, a, b) ∈ ps →
    (packRun v t ps).regs d = some (joinValue (v a) (v b))
  | [], _, _, hm => by simp at hm
  | p :: ps, t, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [packRun, packRun_other v ps _ (fun q hq he => hnd.1 ⟨q, hq, he⟩)]
      simp [PTX.next, setReg]
    · exact packRun_val v ps _ hnd.2 hm

/-- **A run of packs**: each writes its joined pair when every source word has four bytes;
otherwise the thread is dead. -/
theorem packs_run (hN : NoPack A) (v : Nat → Value) : ∀ (ps : List (Nat × Nat × Nat)) (t : TState),
    PackCode K t.pc ps → t.fault = none →
    (∀ p ∈ ps, t.regs p.2.1 = some (v p.2.1) ∧ t.regs p.2.2 = some (v p.2.2)) →
    (∀ p ∈ ps, ∀ q ∈ ps, q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2) →
    (∀ i < ps.length, Assumption.SegFreePc A (t.pc + i)) →
    (packsOk v ps = true → run K A L g ps.length t = some (packRun v t ps)) ∧
    (packsOk v ps = false → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
  | [], t, _, _, _, _, _ => ⟨fun _ => rfl, fun h => by simp [packsOk] at h⟩
  | p :: ps, t, hc, hf, hv, hfr, hS => by
    obtain ⟨ha, hb⟩ := hv p (by simp)
    have hS0 : Assumption.SegFreePc A t.pc := by simpa using hS 0 (by simp)
    have hex := exec_pack (A := A) (L := L) (g := g) (d := p.1) hN ha hb hS0
    set t1 := PTX.next (setReg t p.1 (joinValue (v p.2.1) (v p.2.2)))
    have hreg : ∀ q ∈ ps, t1.regs q.2.1 = some (v q.2.1) ∧ t1.regs q.2.2 = some (v q.2.2) := by
      intro q hq
      have h1 := hfr q (by simp [hq]) p (by simp)
      obtain ⟨ha', hb'⟩ := hv q (by simp [hq])
      simp only [t1, PTX.next, setReg, Function.update_of_ne h1.1.symm,
        Function.update_of_ne h1.2.symm]
      exact ⟨ha', hb'⟩
    have ih := packs_run hN v ps t1 hc.2 hf hreg
      (fun q hq q' hq' => hfr q (by simp [hq]) q' (by simp [hq']))
      (fun i hi => by
        have := hS (i + 1) (by simp; omega)
        rwa [show t.pc + (i + 1) = t1.pc + i by simp [t1, PTX.next, setReg]; omega] at this)
    by_cases h4 : (v p.2.1).bytes = 4 ∧ (v p.2.2).bytes = 4
    · have o1 : out K A L g t = .tau t1 := by
        simp only [out, hf, hc.1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
          Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte, hex, h4, and_self]
      have hok : packsOk v (p :: ps) = packsOk v ps := by simp [packsOk, h4]
      refine ⟨fun h => ?_, fun h => Machine.dead_of_tau o1 (ih.2 (hok ▸ h))⟩
      simp only [List.length_cons, run, tauStep, o1, Option.bind_some, packRun]
      exact ih.1 (hok ▸ h)
    · refine ⟨fun h => absurd h (by simp [packsOk, h4]), fun _ => ?_⟩
      exact Machine.dead_of_ub (f := .typeMismatch) (by
        simp only [out, hf, hc.1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
          Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte, hex, h4])

/-! ### Packed multiplications -/

/-- The packed multiplications `(d, s)` (`mul.f32x2 d, s, c`) from `pc` on. -/
def MulCode (K : Kernel) (c : Nat) : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | pc, m :: ms =>
    K.code[pc]? = some ⟨none, (.float {
      op := .mul, ty := FTy.mk .f32 2, dsts := [some m.1], srcs := [.reg m.2, .reg c] })⟩ ∧
      MulCode K c (pc + 1) ms

/-- `MulCode` decided on the code. -/
def mulCodeB (K : Kernel) (c : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | pc, m :: ms =>
    (match K.code[pc]? with
      | some ⟨none, .float {
          op := .mul, ty := FTy.mk .f32 2, srcTys := [], cmpTy := none, rnd := none, mode := .ieee,
          ftz := false, sat := false, relu := false, oob := false, nanMod := false,
          xorsign := false, absMod := false, dsts := [some d], srcs := [.reg a, .reg c'] }⟩ =>
        d == m.1 && a == m.2 && c' == c
      | _ => false) && mulCodeB K c (pc + 1) ms

theorem MulCode.of_bool {c : Nat} : ∀ {pc : Nat} {ms : List (Nat × Nat)},
    mulCodeB K c pc ms = true → MulCode K c pc ms
  | _, [], _ => trivial
  | pc, m :: ms, h => by
    simp only [mulCodeB, Bool.and_eq_true] at h
    refine ⟨?_, MulCode.of_bool h.2⟩
    have h1 := h.1
    split at h1
    · rename_i d a c' heq
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      rw [heq, h1.1.1, h1.1.2, h1.2]
    · simp at h1

/-- The four elements of the pairs `w` and `c` read as `f32` operands. -/
def mulOk (w c : Value) : Bool :=
  (valFloat .f32 (splitValue 64 w).1).toBool && (valFloat .f32 (splitValue 64 w).2).toBool &&
    (valFloat .f32 (splitValue 64 c).1).toBool && (valFloat .f32 (splitValue 64 c).2).toBool

/-- The pair of products of the pairs `w` and `c`. -/
def mulVal (w c : Value) : Value :=
  .pair (.float .f32 (rd32 (splitValue 64 w).1 * rd32 (splitValue 64 c).1))
    (.float .f32 (rd32 (splitValue 64 w).2 * rd32 (splitValue 64 c).2))

/-- Every multiplication's operands read. -/
def mulsOk (v : Nat → Value) (vc : Value) (ms : List (Nat × Nat)) : Bool :=
  ms.all fun m => mulOk (v m.2) vc

/-- The state after the multiplications, from source values `v` and the pair `vc`. -/
def mulRun (v : Nat → Value) (vc : Value) : TState → List (Nat × Nat) → TState
  | t, [] => t
  | t, m :: ms => mulRun v vc (PTX.next (setReg t m.1 (mulVal (v m.2) vc))) ms

theorem pairMul_eq (a b c : Value) : pairMul a b c = mulVal (joinValue a b) c := rfl

theorem pairOk_eq (a b c : Value) :
    pairOk a b c = (a.bytes == 4 && b.bytes == 4 && mulOk (joinValue a b) c) := by
  simp only [pairOk, mulOk, Bool.and_assoc]

theorem mulRun_skel (v : Nat → Value) (vc : Value) : ∀ (ms : List (Nat × Nat)) (t : TState),
    (mulRun v vc t ms).pc = t.pc + ms.length ∧ (mulRun v vc t ms).sub = t.sub ∧
      (mulRun v vc t ms).acc = t.acc ∧ (mulRun v vc t ms).fault = t.fault
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | m :: ms, t => by
    obtain ⟨h1, h2, h3, h4⟩ := mulRun_skel v vc ms (PTX.next (setReg t m.1 (mulVal (v m.2) vc)))
    refine ⟨?_, h2, h3, h4⟩
    rw [mulRun, h1]
    simp only [PTX.next, setReg, List.length_cons]
    omega

/-- A register no multiplication writes keeps its value. -/
theorem mulRun_other (v : Nat → Value) (vc : Value) {r : Nat} :
    ∀ (ms : List (Nat × Nat)) (t : TState), (∀ m ∈ ms, m.1 ≠ r) →
      (mulRun v vc t ms).regs r = t.regs r
  | [], _, _ => rfl
  | m :: ms, t, h => by
    rw [mulRun, mulRun_other v vc ms _ (fun q hq => h q (by simp [hq]))]
    simp [PTX.next, setReg, Function.update_of_ne (h m (by simp)).symm]

/-- The destination of a multiplication holds its products, when no other one writes it. -/
theorem mulRun_val (v : Nat → Value) (vc : Value) {d s : Nat} : ∀ (ms : List (Nat × Nat))
    (t : TState), (ms.map Prod.fst).Nodup → (d, s) ∈ ms →
    (mulRun v vc t ms).regs d = some (mulVal (v s) vc)
  | [], _, _, hm => by simp at hm
  | m :: ms, t, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [mulRun, mulRun_other v vc ms _ (fun q hq he => hnd.1 ⟨q, hq, he⟩)]
      simp [PTX.next, setReg]
    · exact mulRun_val v vc ms _ hnd.2 hm

/-- `pairOk` false on words of four bytes is `mulOk` false on the packed pair. -/
theorem pairOk_false_iff {va vb vc : Value} (h4a : va.bytes = 4) (h4b : vb.bytes = 4) :
    (pairOk va vb vc = false ↔ mulOk (joinValue va vb) vc = false) := by
  simp [pairOk, mulOk, h4a, h4b]

/-- The three ways the pair reads of a packed multiplication can go: a fault (`PairFault`: the
thread is dead), a NaN (the rule declines and the Core rule applies) or two numbers. -/
theorem pairRead_dichotomy (w c : Value) :
    PairFault w c ∨ pairRead w = none ∨
      (∃ p, pairRead w = some (.ok p)) ∧ pairRead c = none ∨
        ∃ p q, pairRead w = some (.ok p) ∧ pairRead c = some (.ok q) := by
  unfold PairFault
  cases pairRead w with
  | none => simp
  | some e =>
    cases e with
    | error f => simp
    | ok p =>
      cases pairRead c with
      | none => simp
      | some e2 =>
        cases e2 with
        | error f => simp
        | ok q => simp

/-- `mulOk` false: one of the three cases of `pairRead_dichotomy` holds, so the step either faults
(the thread is dead, `mul_step`), declines (the Core rule applies) or reads an infinity (the ideal
rule gives a result that is not `mulVal`). -/
theorem mulOk_false_cases {w c : Value} : mulOk w c = false →
    PairFault w c ∨ pairRead w = none ∨
      (∃ p, pairRead w = some (.ok p)) ∧ pairRead c = none ∨
        ∃ p q, pairRead w = some (.ok p) ∧ pairRead c = some (.ok q) :=
  fun _ => pairRead_dichotomy w c

/-- One multiplication: a local step to its products when its operands read, and a dead thread
when a pair it reads faults (`PairFault`). -/
theorem mul_step {t : TState} (hA : Assumption.IdealAt A .mulF32x2 L g t) {d a c : Nat}
    {w vc : Value} (hc : K.code[t.pc]? = some ⟨none, (.float {
      op := .mul, ty := FTy.mk .f32 2, dsts := [some d], srcs := [.reg a, .reg c] })⟩)
    (hf : t.fault = none) (ha : t.regs a = some w) (hcv : t.regs c = some vc) :
    (mulOk w vc = true → out K A L g t = .tau (PTX.next (setReg t d (mulVal w vc)))) ∧
    (PairFault w vc → Machine.Dead (K := K) (A := A) (L := L) (g := g) t) := by
  constructor
  · intro hok
    simp only [mulOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hx0, hx1⟩, hy0⟩, hy1⟩ := hok
    obtain ⟨x0, hx0⟩ := ok_of_toBool hx0
    obtain ⟨x1, hx1⟩ := ok_of_toBool hx1
    obtain ⟨y0, hy0⟩ := ok_of_toBool hy0
    obtain ⟨y1, hy1⟩ := ok_of_toBool hy1
    simp only [out, hf, hc, guardHolds, pure, Except.pure, Op.isLocal, ↓reduceIte,
      exec_fmul2 hA ha hcv hx0 hx1 hy0 hy1, hx0, hx1, hy0, hy1, mulVal, rd32, Except.toOption,
      Option.getD_some]
  · intro hbad
    obtain ⟨f, hfl⟩ := exec_fmul2_error (d := d) hA ha hcv hbad
    exact Machine.dead_of_ub (f := f) (by
      simp only [out, hf, hc, guardHolds, pure, Except.pure, Op.isLocal, ↓reduceIte]
      rw [hfl])

/-- Some multiplication of the run reads a pair that faults (`PairFault`), the ones before it
reading as numbers: the run is dead from there. A NaN or an infinity operand is no such case. -/
def mulsFaults (v : Nat → Value) (vc : Value) : List (Nat × Nat) → Prop
  | [] => False
  | m :: ms => PairFault (v m.2) vc ∨ (mulOk (v m.2) vc = true ∧ mulsFaults v vc ms)

/-- **A run of packed multiplications**: each writes its products when the operands of every one
read; otherwise the thread is dead. -/
theorem muls_run (v : Nat → Value) {c : Nat} {vc : Value} : ∀ (ms : List (Nat × Nat))
    (t : TState), MulCode K c t.pc ms → t.fault = none → t.regs c = some vc →
    (∀ m ∈ ms, t.regs m.2 = some (v m.2)) →
    (∀ m ∈ ms, m.1 ≠ c ∧ ∀ m' ∈ ms, m.1 ≠ m'.2) →
    (∀ i < ms.length, ∀ s : TState, s.pc = t.pc + i → Assumption.IdealAt A .mulF32x2 L g s) →
    (mulsOk v vc ms = true → run K A L g ms.length t = some (mulRun v vc t ms)) ∧
    (mulsFaults v vc ms → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
  | [], t, _, _, _, _, _, _ => ⟨fun _ => rfl, fun h => h.elim⟩
  | m :: ms, t, hc, hf, hcv, hv, hfr, hI => by
    have hs := mul_step (hI 0 (by simp) t (by simp)) hc.1 hf (hv m (by simp)) hcv
    set t1 := PTX.next (setReg t m.1 (mulVal (v m.2) vc))
    have hm := hfr m (by simp)
    have hcv1 : t1.regs c = some vc := by
      simp [t1, PTX.next, setReg, Function.update_of_ne hm.1.symm, hcv]
    have hreg : ∀ q ∈ ms, t1.regs q.2 = some (v q.2) := by
      intro q hq
      simp only [t1, PTX.next, setReg, Function.update_of_ne (hm.2 q (by simp [hq])).symm]
      exact hv q (by simp [hq])
    have ih := muls_run v ms t1 hc.2 hf hcv1 hreg
      (fun q hq => ⟨(hfr q (by simp [hq])).1,
        fun q' hq' => (hfr q (by simp [hq])).2 q' (by simp [hq'])⟩)
      (fun i hi s hs' => hI (i + 1) (by simp; omega) s
        (by rw [hs']; simp [t1, PTX.next, setReg]; omega))
    cases hok : mulOk (v m.2) vc with
    | true =>
      have o1 := hs.1 hok
      have he : mulsOk v vc (m :: ms) = mulsOk v vc ms := by simp [mulsOk, hok]
      refine ⟨fun h => ?_, fun hf => ?_⟩
      · simp only [List.length_cons, run, tauStep, o1, Option.bind_some, mulRun]
        exact ih.1 (he ▸ h)
      · rcases hf with hbad | ⟨-, htail⟩
        · exact hs.2 hbad
        · exact Machine.dead_of_tau o1 (ih.2 htail)
    | false =>
      refine ⟨fun h => absurd h (by simp [mulsOk, hok]), fun hf => ?_⟩
      rcases hf with hbad | ⟨hok', -⟩
      · exact hs.2 hbad
      · simp [hok] at hok'

end
end PTX.Flow
