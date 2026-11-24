-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueTrace
public import Lemmas.Async.ReadSources
public import Lemmas.Flow.ContinuingEvent
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Kernels.TmlFa4Fwd.Flow.Code.Part051
public import Kernels.TmlFa4Fwd.Flow.Code.Part123
public import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue Epilogue

private def setupHead (producer : Bool) : Nat := if producer then 3274 else 7932
private def setupLength (producer : Bool) : Nat := if producer then 9 else 3

private theorem setupCore (producer : Bool) :
    ((kernel.code.drop (setupHead producer)).take (setupLength producer)).all
      (fun ins => Assumptions.coreOp ins.op) = true := by
  cases producer <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem setupFallthrough (producer : Bool) :
    ((kernel.code.drop (setupHead producer)).take (setupLength producer-1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  cases producer <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem setupTransparent (producer : Bool) {l : Launch} {g : Nat} {s : TState}
    (hLo : setupHead producer ≤ s.pc) (hHi : s.pc < setupHead producer+setupLength producer) :
    out kernel Assumptions.all l g s = out kernel [] l g s := by
  cases hc : kernel.code[s.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hMem : ins ∈ (kernel.code.drop (setupHead producer)).take (setupLength producer) := by
      apply List.mem_of_getElem? (i := s.pc - setupHead producer)
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp (setupCore producer) _ hMem)
    all_goals
      cases producer <;>
        simp only [setupHead, setupLength, Bool.false_eq_true, ↓reduceIte,
          Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites, Assumptions.delayedTmemSites,
          List.mem_cons, List.not_mem_nil, or_false] at hLo hHi ⊢ <;>
        omega

private theorem transportSetup (producer : Bool) {l : Launch} {g : Nat} {s u : TState}
    (hs : s.pc = setupHead producer) (hr : run kernel [] l g (setupLength producer) s = some u) :
    run kernel Assumptions.all l g (setupLength producer) s = some u :=
  schedulerLocalTransport (setupFallthrough producer)
    (fun hlo hhi => setupTransparent producer hlo hhi) hr hs.ge (by rw [hs])

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The statistics barrier setup uses the local integer semantics on the softmax prefix. -/
theorem softmaxStatsBarrierCore (l : Launch) (g : Nat) (warp : Fin 8) :
    Seg kernel [] l g 9 3274 [(1062, b32 warp.val)] 3283 [(5127, b32 (3 + warp.val))] := by
  fin_cases warp <;> intro t ht <;> seg_fp ht using seg_close

/-- Both softmax groups compute the barrier ID for their own statistics lane group. -/
theorem softmaxStatsBarrierSetup (l : Launch) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 9 3274 [(1062, b32 warp.val)] 3283
      [(5127, b32 (3 + warp.val))] := by
  intro t ht
  obtain ⟨u, hu, hs⟩ := softmaxStatsBarrierCore l g warp t ht
  exact ⟨u, transportSetup true ht.1 hu, hs⟩

private theorem correctionRawStep {l : Launch} {g pc : Nat} {t u : TState} {op : Op}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hp : t.pc = pc) (hf : t.fault = none) (he : execLocal l g t op = .ok u) :
    run kernel [] l g 1 t = some u := by
  simp only [run, tauStep, out, hp, hf, hc, guardHolds, hl, ↓reduceIte, execLocalA_nil, he]
  rfl

/-- The correction setup uses only integer registers and therefore leaves any already present
scratch fields alone. This is the same straight-line register segment with a weaker entry. -/
theorem correctionStatsBarrierRaw {l : Launch} {g : Nat} (warp : Fin 16) {t : TState}
    (hp : t.pc = 7932) (hf : t.fault = none) (hw : t.regs 1062 = some (b32 warp.val)) :
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧ u.pc = 7935 ∧
      u.regs 1625 = some (b32 (warp.val % 4 + 3)) ∧
      u.regs 1626 = some (b32 (warp.val % 4 + 7)) := by
  let w := warp.val
  let k := w % 4
  let s := next (setReg t 5950 (b32 k))
  let u := next (setReg s 1625 (b32 (k+3)))
  let v := next (setReg u 1626 (b32 (k+7)))
  have hWarp : w < 16 := warp.isLt
  have hK : k < 4 := Nat.mod_lt _ (by decide)
  have hAnd : w &&& 3 = k := Nat.and_two_pow_sub_one_eq_mod w 2
  have hCode := Flow.code_7932
  have he : execLocal l g t (.int ⟨.and, .int .b 32, false, [some 5950],
      [.reg 1062, .imm 3]⟩) = .ok s := by
    have hA := readBits_b32 (L := l) (g := g) (a := w) hw (by omega)
    have hB : readBits l g t 32 (.imm 3) = .ok 3#64 := rfl
    change (do
      let x ← readBits l g t 32 (.reg 1062)
      let y ← readBits l g t 32 (.imm 3)
      pure (next (setReg t 5950 (.bits 32 (x &&& y))))) = .ok s
    rw [hA, hB]
    have hBits : BitVec.ofNat 64 w &&& 3#64 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_and, toNat_ofNat_lt (show w < 2^64 by omega),
        toNat_ofNat_lt (show k < 2^64 by omega), hAnd]
    change Except.ok (next (setReg t 5950 (.bits 32 (BitVec.ofNat 64 w &&& 3#64)))) = _
    rw [hBits]
    rfl
  have ha := correctionRawStep hCode rfl hp hf he
  have hAdd {q : TState} {dst off : Nat} (hOff : off ≤ 7)
      (hq : q.regs 5950 = some (b32 k)) :
      execLocal l g q (.int ⟨.add, .int .s 32, false, [some dst],
        [.reg 5950, .imm off]⟩) = .ok (next (setReg q dst (b32 (k+off)))) := by
    have hoff : off < 2^32 := by omega
    have hk : k < 2^32 := by omega
    have hsum : k+off < 2^32 := by omega
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readValue, readBits, readReg, hq, b32, bind, Except.bind,
      pure, Except.pure, BitVec.ofInt_natCast, truncBits_ofNat hoff (by decide),
      truncBits_ofNat hk (by decide)]
    change Except.ok (next (setReg q dst (.bits 32 (truncBits 32
      (BitVec.ofNat 64 k + BitVec.ofNat 64 off))))) = _
    rw [← BitVec.ofNat_add, truncBits_ofNat hsum (by decide)]
  have hsPc : s.pc = 7933 := congrArg (·+1) hp
  have huPc : u.pc = 7934 := congrArg (·+1) hsPc
  have hs : s.regs 5950 = some (b32 k) := by simp [s, next, setReg]
  have hu : u.regs 5950 = some (b32 k) := by simp [u, next, setReg, hs]
  have hb := correctionRawStep Flow.code_7933 rfl hsPc hf (hAdd (off := 3) (by decide) hs)
  have hc := correctionRawStep Flow.code_7934 rfl huPc hf (hAdd (off := 7) (by decide) hu)
  exact ⟨v, transportSetup false hp (run_comp (run_comp ha hb) hc),
    congrArg (·+1) huPc, by simp [v, u, next, setReg, k, w], by simp [v, next, setReg, k, w]⟩

end PTX.Kernels.TmlFa4Fwd
