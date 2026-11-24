-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmBase
public import Kernels.InklingRelDecode.Proof.Thread.EvDFires
public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiStore

@[expose] public section

/-! # Global loads and stores: not undefined behaviour at an aligned address

The kernel's global loads (`gload`, `ld.global.b16` and `.b32` through a 64-bit register at
offset 0) and 32-bit global stores (`gstore32`) have an undefined-behaviour template only if the
address register does not hold a 64-bit number, is misaligned, or the stored register does not
have four bytes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **An aligned global load is not undefined behaviour.** -/
theorem gload_ok {base dst a w : Nat} (hr : t.regs base = some (b64 a)) (ha : a < 2 ^ 64)
    (hw : w = 16 ∨ w = 32) (hal : a % (w / 8) = 0) (f : Fault) :
    eventTmpl A L g t (.mem (gload base dst w)) ≠ .ub f := by
  have hrule : (gload base dst w).rule = some .threadAccess := by
    unfold gload; rcases hw with rfl | rfl <;> rfl
  have hww : (gload base dst w).elem.width = w := by
    unfold gload; rcases hw with rfl | rfl <;> rfl
  have hw8 : 0 < w / 8 := by rcases hw with rfl | rfl <;> decide
  refine loadDirect_ok (sp := .global) hrule rfl rfl rfl rfl rfl (by rw [hww]; exact hw8) ?_ f
  refine ⟨⟨.global, 0, a⟩, effAddr_global hr ha, ?_⟩
  show a % ((gload base dst w).elem.width / 8 * 1) = 0
  rw [hww]
  simpa using hal

/-- **An aligned 32-bit global store of a four-byte register is not undefined behaviour.** -/
theorem gstore32_ok {base src a : Nat} {v : Value} (hs : t.sub = 0)
    (hr : t.regs base = some (b64 a)) (ha : a < 2 ^ 64) (hv : t.regs src = some v)
    (hb : v.bytes = 4) (hal : a % 4 = 0) (f : Fault) :
    eventTmpl A L g t (.mem (gstore32 base src)) ≠ .ub f := by
  have hrule : (gstore32 base src).rule = some .threadAccess := by unfold gstore32; rfl
  refine storeDirect_ok (sp := .global) hrule rfl rfl rfl rfl (by simp [gstore32, DType.width])
    ?_ (o := .reg src) (by simp [gstore32, hs]) ⟨v, readValue_reg hv, ?_⟩ f
  · exact ⟨⟨.global, 0, a⟩, effAddr_global hr ha, by simpa [gstore32, DType.width] using hal⟩
  · simpa [gstore32, DType.width] using hb

end
end PTX.Kernels.InklingRelDecode.Proof.Tm
