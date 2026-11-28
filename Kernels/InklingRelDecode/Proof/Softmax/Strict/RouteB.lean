-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteP
import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreAddress
import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreGate
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Pointers
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Init
import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants
public import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Flow.Code
import Lemmas.Flow.Arith32Word
@[expose] public section
/-! The setup after the first barrier, run exactly: pcs 576 to 600 and 602 to 679 -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

set_option hygiene false in
macro "bz_idx" : tactic => `(tactic|
  (simp only [Control.valueOf, Control.scalarValue, Control.u32, Control.u16, Control.u64,
    Nat.reduceEqDiff, ↓reduceIte]
   all_goals first
    | rfl
    | (generalize eqt : _ % Launch.block _ = tid at hT ⊢
       clear eqt
       revert tid
       decide +kernel)
    | (norm_bits [Control.row, Control.token, Control.headInGroup]; done)
    | (norm_cmp [Control.row, Control.token, Control.validRow]; done)))

pre_seg bz_576 576 580 BF, BF using bz_idx
pre_seg bz_580 580 584 BF, BF using bz_idx
pre_seg bz_584 584 585 BF, BF using bz_idx
pre_seg bz_586 586 587 BF, BF using simp [Control.valueOf, Control.scalarValue, Control.validRow]
pre_seg bz_587 587 589 BF, BF using bz_idx

pre_seg bz_585 585 586 BF, BF using
  have tok : Control.token (g % L.block) < 2 ^ 31 := by unfold Control.token Control.row; omega
  exact congrArg Value.pred (Control.cmp_gt_signed _ _ ok.query tok)

pre_seg bz_589 589 597 BF, BF using bz_idx
pre_seg bz_597 597 598 BF, BF using norm_bits [Control.valueOf, Control.scalarValue, Control.u32]

/-- **One local instruction run exactly**: it writes `d` with `v`, the facts after are the facts
before and the new one. -/
theorem seg_one {pc d : Nat} {op : Op} {F G : List (Nat × Value)} {v : Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc F → execLocalA Assumptions.all L g t op = .ok (PTX.next (setReg t d v)))
    (hG : ∀ p ∈ G, p = (d, v) ∨ (p ∈ F ∧ p.1 ≠ d)) :
    Seg kernel Assumptions.all L g 1 pc F (pc + 1) G := by
  intro t h
  obtain ⟨hpc, hsub, hacc, hflt, hregs⟩ := h
  refine ⟨_, run_local hc hl ⟨hpc, hsub, hacc, hflt, hregs⟩ (hex t ⟨hpc, hsub, hacc, hflt, hregs⟩),
    congrArg (· + 1) hpc, hsub, hacc, hflt, ?_⟩
  refine holds_of_mem fun r x hm => ?_
  rcases hG _ hm with h' | ⟨hp, hne⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    simp [PTX.next, setReg]
  · simp only [PTX.next, setReg]
    rw [Function.update_of_ne hne]
    exact holds_mem hregs hp

theorem add_ok {t : TState} {dst r δ : Nat} {w : Value} {x : BitVec 64} {op : Opnd}
    (hr : t.regs r = some w) (hw : w.regBits = some x)
    (hv : readValue L g t 32 op = .ok (b32 δ)) (hb : readBits L g t 32 op = .ok (Arith32.W δ)) :
    ∃ u, execInt L g t ⟨.add, .int .s 32, false, [some dst], [.reg r, op]⟩ = .ok u := by
  have hx := readBits_regBits (L := L) (g := g) (w := 32) hr hw
  have hv' : readValue L g t 32 (.reg r) = .ok w := by simp [readValue, readReg, hr]; rfl
  cases w <;> first
    | (simp [Value.regBits] at hw; done)
    | (simp only [execInt, DType.width, hv', hv, hb, hx, b32, bind, Except.bind, pure,
        Except.pure]
       exact ⟨_, rfl⟩)

theorem first_sum (ok : e.Ok) (δ : Nat) :
    Lib.addBase e.firstWord δ = Control.u32 (e.firstToken + δ) := by
  have bits := ok.firstBits
  unfold Control.Entry.firstToken
  cases h : e.firstWord <;> simp_all [Lib.addBase, Control.u32]
  change false = true at bits
  contradiction

/-- **A local instruction that writes a datum**, with the written word known (the proofs may use
the tags that hold before it). -/
theorem segQF_set {qt : Nat → EnvF} {pc d : Nat} {tg : TagF} {op : Op} {F G : List (Nat × Value)}
    {v : Value} (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc F → TypedF (qt pc) t →
      execLocalA Assumptions.all L g t op = .ok (PTX.next (setReg t d v)))
    (hv : ∀ t, At t pc F → TypedF (qt pc) t → tg.ok (some v))
    (hq : afterF qt pc [(d, tg)] = true) (hG : ∀ p ∈ G, p = (d, v) ∨ (p ∈ F ∧ p.1 ≠ d)) :
    SegQ kernel Assumptions.all L g (QTF qt) pc F (pc + 1) G := by
  intro t ht hQ
  obtain ⟨hpc, hsub, hacc, hflt, hregs⟩ := id ht
  have hty : TypedF (qt pc) t := by simpa [QTF, hpc] using hQ
  have htau := tau_of_ok (A := Assumptions.all) (L := L) (g := g) (by rw [hpc]; exact hc) hl
    hflt (hex t ht hty)
  obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := tg) (hv t ht hty)
  refine ⟨_, .single htau, ⟨by simp [PTX.next, setReg, hpc], hsub, hacc, hflt,
    holds_of_mem fun r x hm => ?_⟩,
    QTF.after1 hQ hpc (by simp [PTX.next, setReg, hpc]) hw1 hw2 hq⟩
  rcases hG _ hm with h | ⟨hp, hne⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [PTX.next, setReg]
  · simp only [PTX.next, setReg]
    rw [Function.update_of_ne hne]
    exact holds_mem hregs hp

/-- The entry's word is among the facts of the setup. -/
theorem bf_entry {v : Control.Carry} (pc : Nat) : (525, Data.scaleVal L) ∈ BF e L g v pc :=
  List.mem_append_left _ (by simp [Data.dF, Data.dFS, Data.entryFact])

theorem bz_598 {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) :
    Seg kernel Assumptions.all L g 1 598 (BF e L g v 598) 599 (BF e L g v 599) := by
  have small : Control.token (g % L.block) < 2 ^ 31 := by
    have := hT
    unfold Control.token Control.row
    omega
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ok.firstBits
  refine seg_one (d := 803) (v := Control.valueOf e L g ⟨.bar0, 0, v⟩ 803) Flow.code_598 rfl
    (fun t ht => ?_) (fun p hp => ?_)
  · obtain ⟨hpc, -, -, -, hregs⟩ := ht
    have hF := ((holds_append _ _ _).mp hregs).2
    have h610 : t.regs 610 = some e.firstWord := holds_mem hF (mem_factsFrom (by decide +kernel))
    obtain ⟨hv, hb⟩ := Lib.delta_reg (L := L) (g := g) (r := 496) hF (by decide +kernel)
      (δ := Control.token (g % L.block)) rfl (by unfold Control.token Control.row; omega)
    obtain ⟨u, hu⟩ := add_ok (dst := 803) h610 hx hv hb
    have := Lib.raw_add (L := L) (g := g) false h610 small hv hb hu
    rw [Lib.workerInt (by rfl) hpc (by decide), hu, this, first_sum ok]
    simp [Control.valueOf, Control.scalarValue]
  · rcases List.mem_append.mp hp with h | h
    · refine .inr ⟨List.mem_append_left _ h, ?_⟩
      obtain rfl : p = (525, Data.scaleVal L) := by
        simpa [Data.dF, Data.dFS, Data.entryFact] using h
      simp
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      by_cases h803 : r = 803
      · subst h803; exact .inl rfl
      · exact .inr ⟨List.mem_append_right _ (mem_factsFrom
          ((by decide +kernel : ∀ r ∈ Control.ctlLive 599, r ≠ 803 → r ∈ Control.ctlLive 598)
            r hr h803)), h803⟩

/-- The scale parameter of the launch is a nonzero number (`Pre`'s scale is positive). -/
def ScaleOk (L : Launch) : Prop :=
  ∃ s : ℝ, valFloat .f32 (Data.scaleVal L) = .ok s ∧ s ≠ 0

/-- The launch's scale parameter is a nonzero number whenever the preconditions hold. -/
theorem ScaleOk.of_pre {Q : Params} {m : Mem0} (hp : Pre Q L m) : ScaleOk L :=
  ⟨Q.scale, Data.scaleVal_float hp, hp.scalePos.ne'⟩

theorem scaleW_float {s : ℝ} (hy : valFloat .f32 (Data.scaleVal L) = .ok s) :
    Data.scaleW L = .float .f32 (s * log2eF32) := by
  simp [Data.scaleW, Lib.scaleWord, xFinal, XItem.upd, XItem.vals, Lib.scaleItem, regsOf, regOf,
    fF, mulL, fOpnd, lk, List.flatMap, mulE_fin hy Data.valFloat_log2e, okVal]

/-- **The scale multiplication of pc 601** writes the scale word when the parameter is a number. -/
theorem exec_scale {s : ℝ} (hy : valFloat .f32 (Data.scaleVal L) = .ok s) {F : List (Nat × Value)}
    (h5 : (525, Data.scaleVal L) ∈ F) {t : TState} (ht : At t 601 F) :
    execLocalA Assumptions.all L g t Lib.scaleItem.op =
      .ok (PTX.next (setReg t 498 (Data.scaleW L))) := by
  have hat := (Lib.scale_at (L := L) (g := g)).1
  obtain ⟨hpc, -, -, -, hregs⟩ := ht
  have hr : ∀ r ∈ Lib.scaleItem.reads, t.regs r = some (Data.iniV L r) := by
    intro r hr
    obtain rfl : r = 525 := by simpa [XItem.reads, Lib.scaleItem, regsOf, regOf] using hr
    simpa [Data.iniV] using holds_mem hregs h5
  have hx := XItem.exec Lib.scaleItem (V := Data.iniV L) (t := t) (hpc ▸ hat.2.1)
    (hat.2.2 t hpc) hr rfl
  have hc : Lib.scaleItem.cond (Data.iniV L) := by
    refine ⟨.float .f32 (s * log2eF32), ?_⟩
    simp only [regsOf, fF, mulL]
    simp [fOpnd, lk, regOf, List.flatMap, Data.iniV, mulE_fin hy Data.valFloat_log2e]
  rw [hx.1 hc]
  simp [XItem.post, XItem.vals, Data.scaleW, Lib.scaleWord, xFinal, XItem.upd, Data.iniV,
    Lib.scaleItem, regsOf, regOf, List.flatMap]

set_option hygiene false in
macro "bz_addr" : tactic => `(tactic|
  (have off := ok.offsetWord
   simp only [Control.valueOf, Control.scalarValue, Control.u32, Control.u64, Nat.reduceEqDiff,
     ↓reduceIte]
   all_goals norm_bits [Control.biasBase]))

pre_seg bz_602 602 603 PF, PF using
  change Value.bits 64 (truncBits 64 (BitVec.ofInt 64 _)) = Value.bits 64 _
  rw [Control.mul_wide_word]
  simp [Control.sx]
pre_seg bz_603 603 606 PF, PF using bz_addr
pre_seg bz_606 606 607 PF, PF using
  have off := ok.offsetWord
  exact Control.add_unsigned_wide _ _ (Nat.mod_lt _ (by decide))
pre_seg bz_607 607 608 PF, PF using bz_addr
pre_seg bz_608 608 609 PF, PF using
  have off := ok.offsetWord
  exact Control.add_signed_wide _ _
pre_seg bz_609 609 610 PF, PF using bz_addr
pre_seg bz_610 610 611 PF, PF using
  have off := ok.offsetWord
  have hb : (g % L.block / 16 % 2) * 64 < 2 ^ 32 := by omega
  convert Control.add_unsigned_wide _ _ hb using 1
  unfold Control.valueOf Control.scalarValue Control.biasBase Control.u64
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  congr 3
  omega

pre_seg bz_611 611 612 PF, PF using
  have := ok.bias
  have := ok.keyRange
  norm_cmp [Control.valueOf, Control.scalarValue]
pre_seg bz_612 612 613 PF, PF using rfl
pre_seg bz_613 613 614 PF, PF using
  exact congrArg Value.pred (Control.cmp_pos_signed e.blocks ok.blockWord)
pre_seg bz_614 614 615 PF, PF using
  simp [Control.valueOf, Control.scalarValue, Control.preEnabled, Bool.and_comm,
    Bool.and_left_comm, Bool.and_assoc]
pre_seg bz_615 615 616 PF, PF using exact Control.ptr_mad _ _
pre_seg bz_616 616 623 PF, PF using exact Control.ptr_add _ _
pre_seg bz_623 623 630 PF, PF using exact Control.ptr_add _ _
pre_seg bz_630 630 637 PF, PF using exact Control.ptr_add _ _
pre_seg bz_637 637 644 PF, PF using exact Control.ptr_add _ _
pre_seg bz_644 644 651 PF, PF using exact Control.ptr_add _ _
pre_seg bz_651 651 658 PF, PF using exact Control.ptr_add _ _
pre_seg bz_658 658 665 PF, PF using exact Control.ptr_add _ _
pre_seg bz_665 665 672 PF, PF using exact Control.ptr_add _ _
pre_seg bz_672 672 679 PF, PF using exact Control.ptr_add _ _
pre_seg bz_599 599 600 BF, BD using rfl
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
