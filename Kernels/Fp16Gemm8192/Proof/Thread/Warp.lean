-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Flow.Shuffle
public import Lemmas.Flow.Polls
public import Lemmas.Flow.TraceInduction

@[expose] public section

/-! # Every thread learns its warp index

Each thread's first event is the shuffle that broadcasts lane 0's warp index to its warp, so
in an execution every thread receives its own warp index, and its machine continues past the
shuffle with `w = g % L.block / 32`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


namespace Prologue

/-- The warp index of thread `g`. -/
abbrev warpOf (L : Launch) (g : Nat) : Nat := g % L.block / 32

theorem warpOf_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (g : Nat) :
    warpOf L g < 12 := by
  unfold warpOf
  rw [hpre.block]
  omega

/-- The shuffle event: lane 0's operand is the thread's warp index. -/
theorem shfl_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : At t Site.shfl.pc (facts L g ⟨.shfl, 0⟩)) (hc : kernel.code[Site.shfl.pc]? = some ins)
    (hf : Fires Site.shfl.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ recv ok, e = ⟨Site.shfl.pc, .shfl .idx (b32 (warpOf L g)) 0 31 recv ok⟩ := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  have hr9 : t.regs 55 = some (b32 (warpOf L g)) :=
    reg_val h (by table_decide) (by pro_values)
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  simp only [eventTmpl, warpTmpl_shfl_idx, shflTmpl, readBits, readValue, readReg, hr9, b32,
    Value.bytes, hb, pure, Except.pure] at hf
  rw [ite_eq_left (by decide), ite_eq_left trivial, show (truncBits 32 (BitVec.ofInt 64 0)).toNat =
    0 by decide,
    show (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 by decide] at hf
  obtain ⟨recv, ok, he, -⟩ := hf
  exact ⟨recv, ok, he⟩

/-- The first event of thread `g`, fired from the machine's initial state, is the shuffle. -/
theorem first_fired {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {e : Event} {o : Option TState}
    (hf : (code L g).toMachine.Fired (some (code L g).init) e o) :
    ∃ recv ok, e = ⟨Site.shfl.pc, .shfl .idx (b32 (warpOf L g)) 0 31 recv ok⟩ := by
  obtain ⟨t, ins, hat, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
  exact shfl_event hpre hat hc hfire

end Prologue

/-- In an execution every thread's shuffle returns its warp index. -/
theorem first_event {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {e : Event} (he : X.get (g, 0) = some e) :
    e = ⟨Prologue.Site.shfl.pc, .shfl .idx (b32 (Prologue.warpOf L g)) 0 31
      (b32 (Prologue.warpOf L g)) true⟩ := by
  have hfirst : ∀ h < L.threads, ∀ ev, X.get (h, 0) = some ev →
      ∃ recv ok, ev = ⟨Prologue.Site.shfl.pc,
        .shfl .idx (b32 (Prologue.warpOf L h)) 0 31 recv ok⟩ := by
    intro h hh ev hev
    obtain ⟨o, hf⟩ := (Frame.trace (fun _ => sound hpre) hX hh).fired_at hev
      (τ := some (code L h).init) rfl
    exact Prologue.first_fired hpre hh hf
  obtain ⟨recv, ok, rfl⟩ := hfirst g hg e he
  obtain ⟨rfl, rfl⟩ := first_shfl_value hX (by rw [hpre.block]; decide) hfirst
    (fun g h hw => by simp only [Prologue.warpOf, hw.2]) hg he
  rfl

end
end PTX.Kernels.Fp16Gemm8192.Proof
