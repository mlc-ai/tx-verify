-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmGen
public import Lemmas.Flow.EmuStep

@[expose] public section

/-! # The P store: the packs of the single registers and the stores (pcs 999-1013)

The probabilities of the thread's 64 columns are in 24 packed pairs (`%rd46 …`, converted to
`bf16` words by the code before pc 999) and 16 single registers (`%r47 …`). After the named
barrier of pc 999 the code converts the single registers in pairs (`cvt.rn.bf16x2.f32`, pcs
1000-1007, read as the exact `bf16` pair by `Assumptions.bf16Exact`) and sets the store's guard
(`mov.pred %p172, -1`, pc 1008). Then `tcgen05.st` stores the 32 words (pc 1009, the event), its
wait (pc 1010), the address of the `p_ready` barrier (pc 1011), the barrier (pc 1012) and the
arrival of thread 0 (pc 1013). This file gives the execution lemma of the conversion, the
segment of pcs 1000-1009, and the steps of the sites `bar20`, `tmemSt`, `tmemWait` and `bar21`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-! ### The conversion `cvt.rn.bf16x2.f32` -/

/-- The conversion instruction of a pair of `f32` registers to a `bf16x2` register. -/
def cvtP (dst a b : Nat) : CvtInstr :=
  ⟨.packed (.float .bf16) 2, .float .f32, some .rn, false, false, false, false, false, false,
    false, dst, .same, [.reg a, .reg b]⟩

/-- **`cvt.rn.bf16x2.f32 d, a, b` on any operand values**: the outcome `cvtBfE` (the exact pair of
`Assumptions.bf16Exact` where both operands read as extended reals, Core's conversion where one is a
NaN, a fault where one has no `.f32` datum). -/
theorem exec_cvtBfE {t : TState} {dst a b : Nat} {va vb : Value}
    (hS : Assumption.SegFreePc asms t.pc) (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA asms L g t (.cvt (cvtP dst a b)) =
      (cvtBfE va vb).map fun v => PTX.next (setReg t dst v) := by
  have hx := readERealOpnd_reg (fmt := .f32) ha
  have hy := readERealOpnd_reg (fmt := .f32) hb
  have h1 : Assumptions.idealArith.localRule L g t (.cvt (cvtP dst a b)) = none :=
    Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp, cvtP, CvtInstr.widenF16?, CvtInstr.packF16?] at h
  have h2 : Assumptions.approx.localRule L g t (.cvt (cvtP dst a b)) = none :=
    Assumption.approxExact_localRule_none fun f h => by simp [Assumption.ApproxForm.ofOp] at h
  have h4 : Assumptions.lg2Exact.localRule L g t (.cvt (cvtP dst a b)) = none := by
    simp [Assumptions.lg2Exact]
  have h5 : Assumptions.divFullExact.localRule L g t (.cvt (cvtP dst a b)) = none := by
    simp [Assumptions.divFullExact]
  have h6 : Assumptions.negExact.localRule L g t (.cvt (cvtP dst a b)) = none := by
    simp [Assumptions.negExact]
  have h7 : Assumptions.bf16Exact.localRule L g t (.cvt (cvtP dst a b)) =
      Assumption.bindRead (readEReal .f32 va) fun x => Assumption.bindRead (readEReal .f32 vb)
        fun y => some (pure (PTX.next (setReg t dst (.pair (erealValue .bf16 y)
          (erealValue .bf16 x))))) := by
    simp [Assumptions.bf16Exact, cvtP, CvtInstr.plain, hx, hy]
  have hcore : execLocal L g t (.cvt (cvtP dst a b)) =
      (coreCvtBf va vb).map fun v => PTX.next (setReg t dst v) := execLocal_cvtBf ha hb
  rw [hS.exec rfl]
  unfold cvtBfE
  rcases hva : readEReal .f32 va with _ | (e | x)
  · simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5, h6, h7, hva,
      Assumption.bindRead]
    exact hcore
  · simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5, h6, h7, hva,
      Assumption.bindRead]
    rfl
  · rcases hvb : readEReal .f32 vb with _ | (e | y)
    · simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5, h6, h7,
        hva, hvb, Assumption.bindRead]
      exact hcore
    · simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5, h6, h7,
        hva, hvb, Assumption.bindRead]
      rfl
    · simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5, h6, h7,
        hva, hvb, Assumption.bindRead]
      rfl

/-- The instruction at `pc` is `cvt.rn.bf16x2.f32 dst, a, b`. -/
def cvtAt (pc dst a b : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .cvt c⟩ => c == cvtP dst a b
  | _ => false

theorem cvtAt_spec {pc dst a b : Nat} (h : cvtAt pc dst a b = true) :
    kernel.code[pc]? = some ⟨none, .cvt (cvtP dst a b)⟩ := by
  unfold cvtAt at h
  split at h
  · rename_i c hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

theorem cvtAt_p : ∀ j < 8, cvtAt (1000 + j) (1677 + (8 * (j / 2) + 6 + j % 2)) (509 + 2 * j)
    (508 + 2 * j) = true := by decide +kernel
theorem emu_p : ∀ j < 9, Assumptions.emuSites.contains (1000 + j) = false := by decide +kernel
theorem live_p : ∀ j < 8, (509 + 2 * j) ∈ Flow.live (1000 + j) ∧
    (508 + 2 * j) ∈ Flow.live (1000 + j) := by decide +kernel
theorem live_p_next : ∀ j < 8, ∀ r ∈ Flow.live (1000 + j + 1),
    r = 1677 + (8 * (j / 2) + 6 + j % 2) ∨ r ∈ Flow.live (1000 + j) := by decide +kernel

/-- `cvt.rn.bf16x2.f32 %r(1216 + w), %r(48 + 2 j), %r(47 + 2 j)` (pc `1000 + j`, the word
`w = 8 (j / 2) + 6 + j % 2`): the word holds the outcome `D.pwE`, or the thread is dead. -/
theorem seg_cvtP (d : D) {j : Nat} (hj : j < 8) :
    SegD kernel asms L g 1 (1000 + j) (factsAt L g (1000 + j) d) (1000 + j + 1)
      (factsAt L g (1000 + j + 1) d) ((d.pwE (8 * (j / 2) + 6 + j % 2)).toBool = true) := by
  obtain ⟨la, lb⟩ := live_p j hj
  have c1 : colR (2 * j) = 2 * (8 * (j / 2) + 6 + j % 2) := by unfold colR; omega
  have c2 : colR (2 * j + 1) = 2 * (8 * (j / 2) + 6 + j % 2) + 1 := by unfold colR; omega
  have hE : d.pwE (8 * (j / 2) + 6 + j % 2) =
      cvtBfE (d.stg.pv (colR (2 * j + 1))) (d.stg.pv (colR (2 * j))) := by
    rw [c1, c2]
    unfold D.pwE
    simp only [show ¬ ((8 * (j / 2) + 6 + j % 2) % 8 < 6) by omega, ↓reduceIte]
  refine SegD.one (d := 1677 + (8 * (j / 2) + 6 + j % 2)) (cvtAt_spec (cvtAt_p j hj)) rfl
    (fun t h => ?_) (fun x hx _ => ?_) (fun r hr => ?_)
  · have ha := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) la)
    have hb := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) lb)
    have ea : valueOf L g d (509 + 2 * j) = d.stg.pv (colR (2 * j + 1)) := by
      rw [show 509 + 2 * j = 508 + (2 * j + 1) by omega]
      exact valueOf_rP d (by omega)
    rw [ea] at ha
    rw [valueOf_rP d (by omega)] at hb
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree (emu_p j (by omega))
    rw [exec_cvtBfE hS ha hb, hE]
  · rw [valueOf_pw d (by omega)]
    exact okVal_of_ok hx
  · rcases live_p_next j hj r hr with h | h
    · exact .inl h
    · by_cases h' : r = 1677 + (8 * (j / 2) + 6 + j % 2)
      · exact .inl h'
      · exact .inr ⟨h', h⟩

/-- **The eight conversions** (pcs 1000 to 1007). -/
theorem seg_cvts (d : D) : ∀ n, n ≤ 8 →
    SegD kernel asms L g n 1000 (factsAt L g 1000 d) (1000 + n) (factsAt L g (1000 + n) d)
      (∀ j < n, (d.pwE (8 * (j / 2) + 6 + j % 2)).toBool = true) := by
  intro n
  induction n with
  | zero => exact fun _ => (SegD.of_seg (Seg.refl _ _)).iff ⟨fun _ j hj => absurd hj (by omega),
      fun _ => trivial⟩
  | succ n ih =>
    exact fun hn => ((ih (by omega)).comp (seg_cvtP d (j := n) (by omega))).iff
      ⟨fun ⟨h1, h2⟩ j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h1 j hj
        · exact h2,
       fun h => ⟨fun j hj => h j (by omega), h n (by omega)⟩⟩

/-- `mov.pred %p172, -1`, the guard of the store (pc 1008). -/
theorem seg_1008 (d : D) :
    Seg kernel asms L g 1 1008 (factsAt L g 1008 d) 1009 (factsAt L g 1009 d) := by
  intro t h
  sm_seg h

/-- **The conversions and the guard** (pcs 1000 to 1008): from the facts after the barrier to the
facts at the store. -/
theorem seg_pst (d : D) :
    SegD kernel asms L g 9 1000 (factsAt L g 1000 d) 1009 (factsAt L g 1009 d) d.psOk :=
  SegD.of_len ((seg_cvts d 8 (le_refl 8)).comp_seg (seg_1008 d)) rfl

/-! ### The steps -/

theorem live_999 : ∀ r ∈ Flow.live 1000, r ∈ Flow.live 999 := by decide +kernel
theorem live_1009 : ∀ r ∈ Flow.live 1010, r ∈ Flow.live 1009 := by decide +kernel
theorem live_1010 : ∀ r ∈ Flow.live 1011, r ∈ Flow.live 1010 := by decide +kernel

/-- **The named barrier before the P store** (pc 999): the conversions and the guard follow; the
thread is dead where a conversion faults. -/
theorem step_bar20 (hi : Inv L g d) (hs : d.site = .bar20) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 999 := by rw [hs]; rfl
  have hc' : kernel.code[999]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_20)
  have hu := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  subst hu
  have h1 : At (PTX.next t) 1000 (factsAt L g 1000 d) :=
    at_next_live (pc := 999) (pc' := 1000) (hpc ▸ h) rfl rfl live_999
  by_cases hp : d.psOk
  · obtain ⟨t', hr, ht'⟩ := ((seg_pst d) _ h1).1 hp
    exact .inl (.inr ⟨{ d with site := .tmemSt }, t', by simp [next, hs, hp], run_rtg hr, ht',
      inv_late hi (by rw [hs]; trivial) (s := .tmemSt) trivial (fun h => absurd h (by simp))⟩)
  · exact .inr ⟨by simp [next, hs, hp], ((seg_pst d) _ h1).2 hp⟩

/-- **The `tcgen05.st` of the P tile** (pc 1009): the event stores the 32 words. -/
theorem step_tmemSt (hi : Inv L g d) (hs : d.site = .tmemSt) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1009 := by rw [hs]; rfl
  have hc' : kernel.code[1009]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemStore_0)
  have h1677 : t.regs 1676 =
      some (b32 ((d.i % 2 * 128 + d.e.tm + r45 d.stg.bw) % 2 ^ 32)) := by
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 1676 ∈ Flow.live d.site.pc by rw [hpc]; decide +kernel))
    have e1 : valueOf L g d 1676 =
        b32 ((d.i % 2 * 128 + d.e.tm + r45 d.stg.bw) % 2 ^ 32) := by sm_vals
    rw [e1] at this
    exact this
  have hf' := hpc ▸ hf
  obtain ⟨⟨vals, rfl⟩, hu⟩ := fires_tcSt (A := asms) h1677 (Nat.mod_lt _ (by decide)) hf'
  exact step_adv (dn := { d with site := .tmemWait }) (fun _ => hu) (by simp [next, hs])
    (by rw [hpc]; rfl) rfl (by rw [hpc]; exact live_1009)
    (inv_late hi (by rw [hs]; trivial) (s := .tmemWait) trivial (fun h => absurd h (by simp)))
    h hf

/-- `add.s32 d, a, c` of a 32-bit word and a positive immediate below `2 ^ 31`. -/
theorem exec_addPos {t : TState} {d a c x : Nat} (hS : Assumption.SegFreePc asms t.pc)
    (hc : c < 2 ^ 31) (ha : t.regs a = some (b32 x)) :
    execLocalA asms L g t (Op.int ⟨IntOp.add, DType.int IType.s 32, false, [some d],
        [Opnd.reg a, Opnd.imm (c : Int)]⟩) =
      .ok (PTX.next (setReg t d (b32 ((x + c) % 2 ^ 32)))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, IntInstr.rule, execInt, DType.width, readValue, readReg, readBits, ha,
    b32, bind, Except.bind, pure, Except.pure]
  congr 3
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

/-- `add.s32 %r1248, %r44, 213296`, the address of the `p_ready` barrier (pc 1011). -/
theorem seg_1011 (d : D) :
    Seg kernel asms L g 1 1011 (factsAt L g 1011 d) 1012 (factsAt L g 1012 d) := by
  refine seg_one (r := 1709) (v := b32 ((L.sharedBase + d.i % 2 * 8 + 213296) % 2 ^ 32))
    Flow.code_1011 rfl ?_ (by sm_vals) (by decide +kernel)
  intro t h
  have h506 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
    (show 505 ∈ Flow.live 1011 by decide +kernel))
  have e506 : valueOf L g d 505 = b32 ((L.sharedBase + d.i % 2 * 8) % 2 ^ 32) := by sm_vals
  rw [e506] at h506
  have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree (by decide +kernel)
  have := exec_addPos (L := L) (g := g) (d := 1709) hS (c := 213296) (by norm_num) h506
  rw [show ((213296 : Nat) : Int) = 213296 from rfl] at this
  rw [this]
  have e : ((L.sharedBase + d.i % 2 * 8) % 2 ^ 32 + 213296) % 2 ^ 32 =
      (L.sharedBase + d.i % 2 * 8 + 213296) % 2 ^ 32 := by omega
  rw [e]

/-- **`tcgen05.wait::st`** (pc 1010): the address of the barrier follows. -/
theorem step_tmemWait (hi : Inv L g d) (hs : d.site = .tmemWait)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1010 := by rw [hs]; rfl
  have hc' : kernel.code[1010]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemWait_0)
  refine step_seg (dn := { d with site := .bar21 }) (n := 1)
    (fun hf' => (fires_tcWaitSt (hpc ▸ hf')).1) (by simp [next, hs]) (by rw [hpc]; exact live_1010)
    ?_ (inv_late hi (by rw [hs]; trivial) (s := .bar21) trivial
      (fun h => absurd h (by simp))) h hf
  rw [hpc]
  exact seg_1011 d

/-! ### The conversions of the packed pairs (pcs 951-998) -/

/-- `mov.b64 {lo, hi}, %rd`, the halves of a pair of numbers. -/
theorem exec_unpack {t : TState} {a b r : Nat} {lo hi : Value}
    (hS : Assumption.SegFreePc asms t.pc) (hr : t.regs r = some (.pair lo hi))
    (hlo : lo.bytes = 4) (hhi : hi.bytes = 4) :
    execLocalA asms L g t (.move ⟨.unpack, .int .b 64, [some a, some b], [.reg r]⟩) =
      .ok (PTX.next (setReg (setReg t a lo) b hi)) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, hr,
    splitValue, Value.bytes, hlo, hhi, bind, Except.bind, pure, Except.pure]

/-- Two registers written one after the other hold their values, the others keep theirs. -/
theorem holds_set2 {R : Nat → Option Value} {F : List (Nat × Value)} {a b : Nat} {lo hi : Value}
    (h : Holds R F) (ha : ∀ p ∈ F, p.1 ≠ a) (hb : ∀ p ∈ F, p.1 ≠ b) (hab : b ≠ a) :
    Holds (Function.update (Function.update R a (some lo)) b (some hi))
      ((b, hi) :: (a, lo) :: F) :=
  ⟨Function.update_self .., by rw [Function.update_of_ne hab.symm]; exact Function.update_self ..,
    holds_update (holds_update h ha) hb⟩

/-- The instruction at `pc` is `mov.b64 {a, b}, r` (an unpack). -/
def unpackAt (pc a b r : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .move m⟩ => m == ⟨.unpack, .int .b 64, [some a, some b], [.reg r]⟩
  | _ => false

theorem unpackAt_spec {pc a b r : Nat} (h : unpackAt pc a b r = true) :
    kernel.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b 64, [some a, some b], [.reg r]⟩⟩ := by
  unfold unpackAt at h
  split at h
  · rename_i m hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

theorem unpack_code : ∀ q < 24, unpackAt (951 + 2 * q) (1710 + 2 * q) (1711 + 2 * q) (1994 + q) =
    true := by decide +kernel
theorem cvtq_code : ∀ q < 24, cvtAt (952 + 2 * q) (1677 + (8 * (q / 6) + q % 6)) (1711 + 2 * q)
    (1710 + 2 * q) = true := by decide +kernel
theorem emu_pq : ∀ q < 24, Assumptions.emuSites.contains (951 + 2 * q) = false ∧
    Assumptions.emuSites.contains (952 + 2 * q) = false := by decide +kernel
theorem live_pq : ∀ q < 24, (1994 + q) ∈ Flow.live (951 + 2 * q) ∧
    (1710 + 2 * q) ∉ Flow.live (951 + 2 * q) ∧ (1711 + 2 * q) ∉ Flow.live (951 + 2 * q) ∧
    (1677 + (8 * (q / 6) + q % 6)) ∉ Flow.live (951 + 2 * q) ∧
    (1677 + (8 * (q / 6) + q % 6)) ∉ Flow.live (952 + 2 * q) := by decide +kernel
theorem live_pq_next : ∀ q < 24, ∀ r ∈ Flow.live (953 + 2 * q),
    r = 1677 + (8 * (q / 6) + q % 6) ∨ r ∈ Flow.live (951 + 2 * q) := by decide +kernel

/-- **The unpack and the conversion of the pair `%rd(46 + q)`** (pcs `951 + 2 q` and `952 + 2 q`):
the word `%r(1216 + pairW q)` holds the outcome `D.pwE`, or the thread is dead. -/
theorem seg_pq (d : D) {q : Nat} (hq : q < 24) :
    SegD kernel asms L g 2 (951 + 2 * q) (factsAt L g (951 + 2 * q) d) (953 + 2 * q)
      (factsAt L g (953 + 2 * q) d) ((d.pwE (pairW q)).toBool = true) := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := live_pq q hq
  obtain ⟨n1, n2⟩ := emu_pq q hq
  have hw : pairW q = 8 * (q / 6) + q % 6 := rfl
  intro t h
  have hrd := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) l1)
  rw [valueOf_rd d hq] at hrd
  have hS1 : Assumption.SegFreeAt asms L g t := Assumption.SegFreePc.at (segFree n1) h.1
  have e1 := exec_unpackE_at (L := L) (g := g) (lo := 1710 + 2 * q) (hi := 1711 + 2 * q)
    (fun _ _ _ _ => asms_none (by simp) (by simp)) hS1 hrd
  have hE : d.pwE (pairW q) = (unpackE 64 (joinValue (d.stg.pv (2 * pairW q))
      (d.stg.pv (2 * pairW q + 1)))).bind fun p => cvtBfE p.2 p.1 := by
    unfold D.pwE
    simp only [show pairW q % 8 < 6 by rw [hw]; omega, ↓reduceIte]
  rcases hU : unpackE 64 (joinValue (d.stg.pv (2 * pairW q)) (d.stg.pv (2 * pairW q + 1)))
    with f | ⟨lo, hi⟩
  · rw [hU] at e1
    have hd := dead_of_error (by rw [h.1]; exact unpackAt_spec (unpack_code q hq)) rfl
      h.2.2.2.1 e1
    refine ⟨fun hc => ?_, fun _ => hd⟩
    rw [hE, hU] at hc
    cases hc
  rw [hU] at e1 hE
  have r1 := run_local (unpackAt_spec (unpack_code q hq)) rfl h e1
  set t1 := PTX.next (setReg (setReg t (1710 + 2 * q) lo) (1711 + 2 * q) hi) with ht1
  have h1 : At t1 (952 + 2 * q) ((1711 + 2 * q, hi) :: (1710 + 2 * q, lo) ::
      factsAt L g (951 + 2 * q) d) :=
    ⟨by simp [ht1, PTX.next, setReg, h.1]; omega, h.2.1, h.2.2.1, h.2.2.2.1,
      holds_set2 h.2.2.2.2 (facts_ne l2) (facts_ne l3) (by omega)⟩
  have hS2 : Assumption.SegFreePc asms t1.pc := by rw [h1.1]; exact segFree n2
  have e2 := exec_cvtBfE (L := L) (g := g) (dst := 1677 + (8 * (q / 6) + q % 6))
    (a := 1711 + 2 * q) (b := 1710 + 2 * q) hS2 (h1.2.2.2.2.1) (h1.2.2.2.2.2.1)
  simp only [Except.bind] at hE
  rcases hC : cvtBfE hi lo with f | v
  · rw [hC] at e2
    have hd := dead_of_error (by rw [h1.1]; exact cvtAt_spec (cvtq_code q hq)) rfl
      h1.2.2.2.1 e2
    refine ⟨fun hc => ?_, fun _ => dead_of_run r1 hd⟩
    rw [hE, hC] at hc
    cases hc
  rw [hC] at e2 hE
  refine ⟨fun _ => ?_, fun hc => absurd (by rw [hE]; rfl) hc⟩
  have r2 := run_local (cvtAt_spec (cvtq_code q hq)) rfl h1 e2
  have hd : ∀ p ∈ ((1711 + 2 * q, hi) :: (1710 + 2 * q, lo) :: factsAt L g (951 + 2 * q) d),
      p.1 ≠ 1677 + (8 * (q / 6) + q % 6) := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show 1711 + 2 * q ≠ _; omega
    · rcases List.mem_cons.mp hp with rfl | hp
      · show 1710 + 2 * q ≠ _; omega
      · exact facts_ne l4 p hp
  have h2 := At.set (r := 1677 + (8 * (q / 6) + q % 6)) (v := v) h1 hd
  refine ⟨_, run_comp r1 r2, ⟨by rw [h2.1]; omega, h2.2.1, h2.2.2.1, h2.2.2.2.1, ?_⟩⟩
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases live_pq_next q hq r hr with rfl | hl
  · rw [holds_mem h2.2.2.2.2 (List.mem_cons_self ..), valueOf_pw d (by omega), D.pwV, ← hw, hE]
    rfl
  · exact holds_mem h2.2.2.2.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (Flow.mem_factsFrom hl))))

/-- **The 24 unpacks and conversions** (pcs 951 to 998). -/
theorem seg_pqs (d : D) : ∀ n, n ≤ 24 →
    SegD kernel asms L g (2 * n) 951 (factsAt L g 951 d) (951 + 2 * n)
      (factsAt L g (951 + 2 * n) d) (∀ q < n, (d.pwE (pairW q)).toBool = true) := by
  intro n
  induction n with
  | zero => exact fun _ => (SegD.of_seg (Seg.refl _ _)).iff ⟨fun _ j hj => absurd hj (by omega),
      fun _ => trivial⟩
  | succ n ih =>
    intro hn
    have h2 : SegD kernel asms L g 2 (951 + 2 * n) (factsAt L g (951 + 2 * n) d)
        (951 + 2 * (n + 1)) (factsAt L g (951 + 2 * (n + 1)) d)
        ((d.pwE (pairW n)).toBool = true) := by
      have := seg_pq (L := L) (g := g) d (q := n) (by omega)
      rwa [show 953 + 2 * n = 951 + 2 * (n + 1) by omega] at this
    exact SegD.of_len (((ih (by omega)).comp h2).iff
      ⟨fun ⟨h1, h2⟩ j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h1 j hj
        · exact h2,
       fun h => ⟨fun j hj => h j (by omega), h n (by omega)⟩⟩) (by omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
