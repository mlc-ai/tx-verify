-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Mma.Segments
public import Kernels.InklingRelDecode.Proof.Lib.IntStep
public import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
public import Lemmas.Flow.LandsFor
import Lemmas.Flow.Arith32Word
import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # The strict leaves of the MMA warp's scalar spans

The spans of `Compare`, `Offsets` and `Broadcast` end in the terminal alternative when an integer
operand has no bit pattern. When the operands are typed that alternative does not occur: these
are the same spans as strict `Seg` pieces. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof Arith32

/-- A strict segment of some length. -/
def SegE (L : Launch) (g s : Nat) (F : List (Nat × Value)) (b : Nat)
    (G : List (Nat × Value)) : Prop :=
  ∃ n, Seg kernel Assumptions.all L g n s F b G

theorem SegE.of_seg {L : Launch} {g n s b : Nat} {F G : List (Nat × Value)}
    (h : Seg kernel Assumptions.all L g n s F b G) : SegE L g s F b G := ⟨n, h⟩

theorem SegE.comp {L : Launch} {g s p b : Nat} {F G H : List (Nat × Value)}
    (h1 : SegE L g s F p G) (h2 : SegE L g p G b H) : SegE L g s F b H := by
  obtain ⟨m, h1⟩ := h1
  obtain ⟨n, h2⟩ := h2
  exact ⟨m + n, h1.comp h2⟩

theorem SegE.land {L : Launch} {g s b : Nat} {F G : List (Nat × Value)} (h : SegE L g s F b G)
    {C : Flow.Code kernel Assumptions.all L g} {d : C.D} {u : TState} (hu : At u s F)
    (hi : C.inv d) (hb : b = C.pc d) (hG : G = C.facts d) (hs : C.sub d = 0)
    (ha : C.acc d = []) :
    ∃ s, Relation.ReflTransGen (Tau kernel Assumptions.all L g) u s ∧ C.Good (some d) s := by
  subst hb hG
  obtain ⟨n, h⟩ := h
  exact Code.landsFor hu h hi hs ha

/-- A one-register integer step that evaluates. -/
theorem scalarStepS {L : Launch} {g pc : Nat} {ii : IntInstr} {F G : List (Nat × Value)}
    {r : Nat} {v : Value} (hc : kernel.code[pc]? = some ⟨none, .int ii⟩)
    (hl : (Op.int ii).isLocal = true) (hr : ii.rule = some .threadInt)
    (hs : Assumptions.emuSites.contains pc = false)
    (hex : ∀ t, Holds t.regs F → execInt L g t ii = .ok (PTX.next (setReg t r v)))
    (hw : ∀ R, Holds R F → Holds (Function.update R r (some v)) G) :
    SegE L g pc F (pc + 1) G := by
  refine ⟨1, fun t ht => ?_⟩
  obtain ⟨hp, hsub, hacc, hf, hF⟩ := ht
  have heval := Lib.workerInt (L := L) (g := g) hr hp hs
  have htau := tau_of_ok (K := kernel) (hp ▸ hc) hl hf (heval.trans (hex t hF))
  exact ⟨PTX.next (setReg t r v), by simp only [run, tauStep_iff.mpr htau, Option.bind_some],
    congrArg (· + 1) hp, hsub, hacc, hf, hw _ hF⟩


variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w d
local notation "V" => valueOf L regs w d
local notation "FF" => liveFacts L regs w

theorem limit_check_s (hw : d.word.regBits.isSome) : SegE L g 2425 (F 2425) 2426 (F 2426) := by
  apply scalarStepS Flow.code_2425 rfl rfl (by decide) (r := 6) (v := V 6)
  · intro t hF
    have hv : t.regs 471 = some d.word :=
      holds_mem hF (mem_factsFrom (val := V) (show 471 ∈ Flow.live 2425 by decide))
    obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.mp hw
    have hx := readBits_regBits (w := 32) (L := L) (g := g) hv hx'
    have hm : readBits L g t 32 (.imm 2147483646) = .ok 2147483646 := rfl
    simp only [execInt, DType.width, hm, hx, bind, Except.bind, pure, Except.pure]
    rw [show truncBits 32 x = truncBits 32 (d.word.regBits.getD 0) by rw [hx']; rfl]
    congr 3
    refine congrArg Value.pred (?_ : _ = decide (2147483646 < d.limit))
    change decide ((d.limit : Int) > 2147483646) = decide (2147483646 < d.limit)
    simp only [decide_eq_decide]
    omega
  · exact fun _ => Lib.writeLive (val := V) (dst := 6) (rs := Flow.live 2425)
      (rs' := Flow.live 2426) (by decide +kernel)

theorem index_check_s (hw : d.word.regBits.isSome) (hi : d.i < 2 ^ 31) (hn : d.limit < 2 ^ 31) :
    SegE L g 2455 (F 2455) 2456 (F 2456) := by
  apply scalarStepS Flow.code_2455 rfl rfl (by decide) (r := 7) (v := V 7)
  · intro t hF
    have hv : t.regs 471 = some d.word :=
      holds_mem hF (mem_factsFrom (val := V) (show 471 ∈ Flow.live 2455 by decide))
    have hctr : t.regs 1911 = some (b32 d.i) :=
      holds_mem hF (mem_factsFrom (val := V) (show 1911 ∈ Flow.live 2455 by decide))
    have hbits : readBits L g t 32 (.reg 1911) = .ok (W d.i) := by
      simpa only [r32_W (by omega : d.i < 2 ^ 32)] using
        (readBits_regBits (L := L) (g := g) (w := 32) hctr (show _ = some (W d.i) from rfl))
    obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.mp hw
    have hx := readBits_regBits (w := 32) (L := L) (g := g) hv hx'
    simp only [execInt, DType.width, hbits, hx, bind, Except.bind, pure, Except.pure]
    have repr : truncBits 32 x = W d.limit := by simp [W, D.limit, low, hx']
    rw [repr]
    congr 3
    refine congrArg Value.pred (?_ : _ = decide (d.limit ≤ d.i))
    change decide (toSigned 32 (W d.i) ≥ toSigned 32 (W d.limit)) = decide (d.limit ≤ d.i)
    rw [toSigned_W hi, toSigned_W hn]
    simp
  · exact fun _ => Lib.writeLive (val := V) (dst := 7) (rs := Flow.live 2455)
      (rs' := Flow.live 2456) (by decide +kernel)

private theorem bits_sum (v : Value) (n : Nat) :
    .bits 32 (truncBits 32 (truncBits 32 (v.regBits.getD 0) + W n)) =
      b32 (((Lib.word v).toNat + n) % 2 ^ 32) := by
  unfold b32 Lib.word
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

/-- A scalar addition of a register with a bit pattern evaluates. -/
theorem raw_add_ok {L : Launch} {g r dst δ : Nat} {t : TState} {w : Value} {op : Opnd}
    (flip : Bool) (hr : t.regs r = some w) (hw : w.regBits.isSome)
    (hv : readValue L g t 32 op = .ok (b32 δ)) (hb : readBits L g t 32 op = .ok (W δ)) :
    execInt L g t ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩ = .ok (PTX.next (setReg t dst (addBase w δ))) := by
  obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.mp hw
  have hx := readBits_regBits (w := 32) (L := L) (g := g) hr hx'
  have hv' : readValue L g t 32 (.reg r) = .ok w := by simp [readValue,readReg,hr]; rfl
  have hb' := bits_sum w δ
  have key : b32 (((Lib.word w).toNat + δ) % 2 ^ 32) =
      Value.bits 32 (truncBits 32 (truncBits 32 x + W δ)) := by
    rw [← hb', hx']
    rfl
  cases w with
  | ptr => simp [Value.regBits] at hx'
  | _ =>
    cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte, execInt, DType.width, hv', hv,
      b32, bind, Except.bind, hb, hx, pure, Except.pure]
    all_goals
      have fin := congrArg (fun v : Value => (Except.ok (PTX.next (setReg t dst v)) :
        Except Fault TState)) key.symm
      first | exact fin | (rw [BitVec.add_comm]; exact fin)

theorem sum_span_s {val : Nat → Value} {rs rs' : List Nat}
    {pc dst r δ : Nat} {op : Opnd} (flip : Bool)
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩⟩) (hs : Assumptions.emuSites.contains pc = false)
    (hr : r ∈ rs) (hbits : (val r).regBits.isSome) (hval : val dst = addBase (val r) δ)
    (hOp : ∀ t, Holds t.regs (factsFrom rs val) → readValue L g t 32 op = .ok (b32 δ) ∧
      readBits L g t 32 op = .ok (W δ))
    (live : ∀ x ∈ rs', x = dst ∨ x ∈ rs)
    (hl : (Op.int ⟨.add, .int .s 32, false, [some dst],
      if flip then [op,.reg r] else [.reg r,op]⟩).isLocal = true := by rfl) :
    SegE L g pc (factsFrom rs val) (pc + 1) (factsFrom rs' val) := by
  apply scalarStepS hc hl (by cases flip <;> rfl) hs (v := val dst)
  · intro t hR
    rw [hval]
    obtain ⟨hv, hb⟩ := hOp t hR
    exact raw_add_ok flip (holds_mem hR (mem_factsFrom hr)) hbits hv hb
  · exact fun _ => Lib.writeLive live

theorem output_base_s (hw : w.regBits.isSome) : SegE L g 2427 (F 2427) 2428 (F 2428) :=
  sum_span_s false (δ := 256) Flow.code_2427 (by decide) (by decide) hw rfl
    (fun _ _ => ⟨rfl, rfl⟩) (by decide)

theorem qk_base_s (hw : w.regBits.isSome) : SegE L g 2472 (F 2472) 2473 (F 2473) :=
  sum_span_s true (δ := 128 * (d.i % 2)) Flow.code_2472 (by decide) (by decide) hw rfl
    (fun _ h => Lib.delta_reg h (show 551 ∈ Flow.live 2472 by decide) rfl (by omega)) (by decide)

theorem pv_base_s (hw : w.regBits.isSome) : SegE L g 2523 (F 2523) 2524 (F 2524) :=
  sum_span_s true (δ := 128 * ((d.i - 1) % 2)) Flow.code_2523
    (by decide) (by decide) hw rfl
    (fun _ h => Lib.delta_reg h (show 569 ∈ Flow.live 2523 by decide) rfl (by omega)) (by decide)

theorem iter_limit_s (hw : d.word.regBits.isSome) (hn : d.limit ≤ 2147483646) :
    SegE L g 2442 (F 2442) 2443 (F 2443) := by
  apply sum_span_s false (δ := 1) Flow.code_2442 (by decide) (by decide) hw _
    (fun _ _ => ⟨rfl, rfl⟩) (by decide)
  change b32 (low d.word + 1) = addBase d.word 1
  change low d.word ≤ 2147483646 at hn
  generalize d.word = v at *
  cases v <;> first | contradiction |
    (change b32 (low _ + 1) = b32 ((low _ + 1) % 2 ^ 32); rw [Nat.mod_eq_of_lt (by omega)])

private theorem guardAt {pc p : Nat} {val : Nat → Value} {t : TState} {b : Bool}
    (h : At t pc (factsFrom (Flow.live pc) val))
    (hm : p ∈ Flow.live pc) (hv : val p = .pred b) :
    At t pc ((p, .pred b) :: factsFrom (Flow.live pc) val) := by
  obtain ⟨hp, hsub, hacc, hf, hR⟩ := h
  exact ⟨hp, hsub, hacc, hf, hv ▸ holds_mem hR (mem_factsFrom hm), hR⟩

local syntax "branch_at " num ppSpace num ppSpace term : tactic
local macro_rules
  | `(tactic| branch_at $reg:num $pc:num $b) => `(tactic| (
    apply SegE.of_seg (n := 1)
    intro t ht
    have state := guardAt (p := $reg) (b := $b) ht (show $reg ∈ Flow.live $pc by decide)
      (by change Value.pred _ = _; congr 1; first | apply decide_eq_true | apply decide_eq_false
          all_goals (try dsimp only [D.limit] at *); omega)
    seg_fp state using rfl))

theorem qk_branch_s (h : d.i < d.limit) : SegE L g 2456 (F 2456) 2457 (F 2457) := by
  branch_at 7 2456 false
theorem pv_branch_s (h : d.limit ≤ d.i) : SegE L g 2456 (F 2456) 2500 (F 2500) := by
  branch_at 7 2456 true
theorem skip_pv_s (h : d.i = 0) : SegE L g 2501 (F 2501) 2447 (F 2447) := by
  branch_at 12 2501 true
theorem enter_pv_s (h : d.i ≠ 0) : SegE L g 2501 (F 2501) 2502 (F 2502) := by
  branch_at 12 2501 false
theorem next_iter_s (h : d.i ≠ d.limit) :
    SegE L g 2454 (FF {d with i := d.i + 1} 2454) 2455 (FF {d with i := d.i + 1} 2455) := by
  branch_at 17 2454 true
theorem end_iter_s (h : d.i = d.limit) :
    SegE L g 2454 (FF {d with i := d.i + 1} 2454) 2550
      (FF {d with i := d.i + 1, site := .finBar} 2550) := by
  branch_at 17 2454 false
theorem within_limit_s (h : d.limit ≤ 2147483646) :
    SegE L g 2426 (F 2426) 2427 (F 2427) := by branch_at 6 2426 false
theorem over_limit_s (h : 2147483646 < d.limit) :
    SegE L g 2426 (F 2426) 2550 (FF {d with site := .finBar} 2550) := by branch_at 6 2426 true

end PTX.Kernels.InklingRelDecode.Proof.Mma
