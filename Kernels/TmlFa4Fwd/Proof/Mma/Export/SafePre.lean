-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Code
public import Lemmas.Flow.TcTmpl
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Mma.Startup
import Lemmas.Flow.LoadShared
import Lemmas.Flow.Step.SiteShape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's allocation prefix is no undefined behaviour

The prefix's `setmaxnreg.dec 80` has a legal count. Its `tcgen05.alloc [sb + 312], %r` (both
sub-steps: the request and the store of the allocated column) addresses the shared base plus 312,
4-aligned, with the register count 512, a valid column count, in a block of whole warps. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- **No event of the allocation prefix is undefined behaviour.** -/
theorem pre_safe (hp : Pre p L m) {s : Start} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (S p L g (ent p L)).AtD s t) (hx : Start.exit s = none)
    (hc : kernel.code[(S p L g (ent p L)).pc s]? = some ins)
    (hf : Fires ((S p L g (ent p L)).pc s) (eventTmpl Assumptions.all L g t ins.op) e o)
    (f : Fault) : e.kind ≠ .ub f := by
  have hreg : ∀ r ∈ Flow.live s.pc, t.regs r = some (valueOf p L g (ent p L) ⟨.bar1, {}⟩ r) :=
    fun r hr => holds_mem hat.2.2.2.2 (mem_factsFrom hr)
  have hsb := hp.shared.2.1
  have hb : L.block % 32 = 0 := by rw [hp.block]
  cases s with
  | set =>
    change kernel.code[1907]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1907)
    refine shape_setMaxReg (P := fun e => e.kind ≠ .ub f) (by simpa [eventTmpl] using hf)
      (by decide) (fun inst => by simp)
  | enter => exact absurd hx (by simp [Start.exit])
  | alloc | wr =>
    change kernel.code[1909]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1909)
    have h1 : t.regs 2535 = some (b32 L.sharedBase) := hreg 2535 (by decide)
    have h2 : t.regs 2451 = some (b32 512) := hreg 2451 (by decide)
    have hd : effAddr L g t .shared 2535 312 =
        .ok ⟨.shared, g / L.block, L.sharedBase + 312⟩ :=
      effAddr_b32_off (L := L) (g := g) (off := 312) h1 (by omega)
    have hn := readBits_b32 (L := L) (g := g) h2 (by decide)
    have hal : (L.sharedBase + 312) % 4 = 0 := by have := hp.shared.1; omega
    intro hk
    have hu := fires_ub hf hk
    simp only [eventTmpl, tcTmpl, hd, hn, bind, Except.bind, ofExec, hb, hal,
      PTX.Proof.toNat_ofNat_lt (show 512 < 2 ^ 64 by decide)] at hu
    revert hu
    simp [Tmem.validColumns, pure, Except.pure]
    split_ifs <;> simp

set_option maxHeartbeats 4000000 in
/-- **The events of the allocation prefix**: the `setmaxnreg.dec 80`, the request of 512 columns
at `sb + 312` (sub-step 0), the store of the allocated column there (sub-step 1). -/
theorem pre_kind (hp : Pre p L m) {s : Start} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (S p L g (ent p L)).AtD s t)
    (hc : kernel.code[(S p L g (ent p L)).pc s]? = some ins)
    (hf : Fires ((S p L g (ent p L)).pc s) (eventTmpl Assumptions.all L g t ins.op) e o) :
    (s = .set → ∃ inst, e.kind = .setMaxReg false 80 inst) ∧
    (s = .alloc → e.kind = .tc (.resource .one (some ⟨.shared, g / L.block, L.sharedBase + 312⟩)
      (.alloc 512))) ∧
    (s = .wr → ∃ col, e.kind = .wr { loc := ⟨.shared, g / L.block, L.sharedBase + 312⟩, size := 4 }
      (Value.bits 32 (BitVec.ofNat 64 col)).toBytes) := by
  have hreg : ∀ r ∈ Flow.live s.pc, t.regs r = some (valueOf p L g (ent p L) ⟨.bar1, {}⟩ r) :=
    fun r hr => holds_mem hat.2.2.2.2 (mem_factsFrom hr)
  have hsb := hp.shared.2.1
  have hb : L.block % 32 = 0 := by rw [hp.block]
  cases s with
  | set =>
    change kernel.code[1907]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1907)
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · intro h; cases h
    · intro h; cases h
    intro _
    refine shape_setMaxReg (P := fun e => ∃ inst, e.kind = .setMaxReg false 80 inst)
      (by simpa [eventTmpl] using hf) (by decide) (fun inst => ⟨inst, rfl⟩)
  | enter => refine ⟨?_, ?_, ?_⟩ <;> (intro h; cases h)
  | alloc | wr =>
    change kernel.code[1909]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1909)
    have h1 : t.regs 2535 = some (b32 L.sharedBase) := hreg 2535 (by decide)
    have h2 : t.regs 2451 = some (b32 512) := hreg 2451 (by decide)
    have hd : effAddr L g t .shared 2535 312 =
        .ok ⟨.shared, g / L.block, L.sharedBase + 312⟩ :=
      effAddr_b32_off (L := L) (g := g) (off := 312) h1 (by omega)
    have hn := readBits_b32 (L := L) (g := g) h2 (by decide)
    have hal : (L.sharedBase + 312) % 4 = 0 := by have := hp.shared.1; omega
    have hsub := hat.2.1
    simp only [eventTmpl, tcTmpl, hd, hn, bind, Except.bind, ofExec, hb, hal,
      PTX.Proof.toNat_ofNat_lt (show 512 < 2 ^ 64 by decide)] at hf
    simp [Tmem.validColumns, pure, Except.pure, hsub] at hf
    first
      | (obtain ⟨hk, -⟩ := hf
         refine ⟨?_, ?_, ?_⟩
         · intro h; cases h
         · intro _; rw [hk]
         · intro h; cases h)
      | (obtain ⟨col, -, hk, -⟩ := hf
         refine ⟨?_, ?_, ?_⟩
         · intro h; cases h
         · intro h; cases h
         · intro _; exact ⟨col, by rw [hk]⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
