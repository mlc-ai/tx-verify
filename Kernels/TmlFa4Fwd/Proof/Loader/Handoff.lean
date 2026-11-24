-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Code
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
import Kernels.TmlFa4Fwd.Proof.Loader.Steps
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' fragment and its hand-off from the startup

The fragment of warps 14 and 15 for lane T1's glue (`Proof/Common`): the loader's machine from
the role's entry, the `setmaxnreg` at pc 179, with the startup's values for the registers live
there that the warp never reads (`ent`). The warp index is the value of register `1062` that the
dispatch compared, so the fragment is indexed by `b : Bool` (warp 14 or 15, `wOf`), and its step
obligations hold at every state (`steps`). The hand-off (`handoff`): a thread state that holds
the startup's facts at `enter loader`, with the shared base `x1 = sharedBase` and the warp word
`x3 = wOf b` that the role's gate fixes, holds the fragment's first facts (`init_facts`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The fragment's step obligations at every state. -/
theorem steps (hp : Pre p L m) (hg : g < L.threads) (b : Bool) (d : (F p L g b).D) :
    (F p L g b).StepAt d :=
  stepAt hp hg (by cases b <;> simp [wOf]) d

theorem live_179 : Flow.live 179 = [1061, 1062, 1069, 1072, 1663, 2390, 2535, 6495, 6497, 7170,
    7289, 7290, 7291, 7292, 7293, 7294, 7295, 7492, 7493, 7494, 7495, 7496, 7497, 7498, 7499,
    7500, 7501, 7502, 7503, 7504, 7505, 7506] := by
  rfl

/-- **The facts of the fragment's first state.** -/
theorem init_facts (p : Params) (L : Launch) (g : Nat) (b : Bool) :
    (F p L g b).facts (F p L g b).init =
      [(1061, b32 (g % L.block)), (1062, b32 (wOf b)), (1069, b32 (L.sharedBase + 192)),
       (1072, .bits 32 (Epilogue.ctaW L g)), (1663, b32 16), (2390, b32 (L.sharedBase + 208)),
       (2535, b32 L.sharedBase), (6495, b32 (L.sharedBase + 144)),
       (6497, b32 (L.sharedBase + 224)), (7170, b32 p.batch),
       (7289, .ptr 64 false (.param (param 11)) 0), (7290, .ptr 64 false (.param (param 10)) 0),
       (7291, .ptr 64 false (.param (param 9)) 0), (7292, b64 (L.localBase + 0)),
       (7293, b64 (L.localBase + 32)), (7294, b64 (L.localBase + 64)),
       (7295, b64 (L.localBase + 96)), (7492, b64 p.kLayout.base),
       (7493, b64 p.kLayout.rowStride), (7494, b64 p.kLayout.headStride),
       (7495, b64 p.kLayout.pageStride), (7496, b64 p.vLayout.base),
       (7497, b64 p.vLayout.rowStride), (7498, b64 p.vLayout.headStride),
       (7499, b64 p.vLayout.pageStride), (7500, b64 p.lseBase), (7501, b64 p.lseStride),
       (7502, b64 p.cuQBase), (7503, b64 p.usedKBase), (7504, b64 p.pageTableBase),
       (7505, b64 p.pageTableStride), (7506, b64 p.cuQBase)] := by
  show Flow.factsFrom (Flow.live 179) (valueOf p L g (wOf b) (ent p L) (D.mk' .setmax {})) = _
  rw [live_179]
  simp [Flow.factsFrom, valueOf, values, valuesRole, valuesStart, ent, List.lookup]

/-- A shared-memory address below `2 ^ 31` as the code's `add.s32` computes it. -/
theorem addi_sb {b n : Nat} (h : b + n < 2 ^ 31) :
    Epilogue.addi (BitVec.ofNat 64 b) n = BitVec.ofNat 64 (b + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Epilogue.addi, Epilogue.r32, Epilogue.i32, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt]
  have h1 : ((n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = n := by omega
  rw [h1]
  simp only [Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show b + n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b + n < 2 ^ 32 by omega)]

/-- The CTA index the startup reads is the thread's CTA. -/
theorem cta_word (hp : Pre p L m) (hg : g < L.threads) :
    Startup.sreg (Startup.ctaX p L g) = BitVec.ofNat 64 (g / L.block) := by
  simp only [Startup.ctaX, Epilogue.params hp]
  have hcta : (L.ctaidOf (g / L.block)).get .x = g / L.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  have hblock : 0 < L.block := by rw [hp.block]; decide
  have hgrid : g / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul hblock).2 (show g < L.grid * L.block from hg)
  have hCta32 : g / L.block < 2 ^ 32 := by have := hp.grid.2.2; omega
  rw [hcta]
  exact truncBits_ofNat hCta32 (by decide)

/-- The batch size as the startup's parameter load reads it. -/
theorem batch_word (hp : Pre p L m) : Startup.sreg p.batch = BitVec.ofNat 64 p.batch :=
  truncBits_ofNat (hp.values (19, p.batch) (by simp [Params.scalarWords])).1 (by decide)

/-- The thread index the startup reads is the lane's index in its CTA. -/
theorem tid_word (hp : Pre p L m) :
    Startup.sreg ((L.tidOf g).get .x) = BitVec.ofNat 64 (g % L.block) := by
  rw [Launch.oneDim_tidOf hp.cluster.2.2]
  have : g % L.block < 2 ^ 32 := by
    have := Nat.mod_lt g (show 0 < L.block by rw [hp.block]; decide)
    rw [hp.block] at this ⊢; omega
  exact truncBits_ofNat this (by decide)

/-- **The hand-off from the startup**: a thread state with the startup's facts at `enter loader`,
whose shared base and warp word are the gate's, holds the facts of the fragment's first state. -/
theorem handoff (hp : Pre p L m) (hg : g < L.threads) (b : Bool) {t : TState} {x2 : BitVec 64}
    (hF : Holds t.regs (Startup.facts p L g
      ⟨.enter .loader, BitVec.ofNat 64 L.sharedBase, x2, BitVec.ofNat 64 (wOf b)⟩)) :
    Holds t.regs ((F p L g b).facts (F p L g b).init) := by
  rw [init_facts]
  have hb := hp.shared.2.1
  have e1 := addi_sb (b := L.sharedBase) (n := 192) (by omega)
  have e2 := addi_sb (b := L.sharedBase) (n := 208) (by omega)
  have e3 := addi_sb (b := L.sharedBase) (n := 144) (by omega)
  have e4 := addi_sb (b := L.sharedBase) (n := 224) (by omega)
  simp only [Nat.cast_ofNat] at e1 e2 e3 e4
  have e6 := cta_word hp hg
  have e7 := batch_word hp
  have e8 := tid_word (g := g) hp
  have hv : ∀ r ∈ Flow.live 179, t.regs r = some (Startup.valueOf p L g
      ⟨.enter .loader, BitVec.ofNat 64 L.sharedBase, x2, BitVec.ofNat 64 (wOf b)⟩ r) :=
    fun r hr => holds_mem hF (mem_factsFrom hr)
  simp only [live_179, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ := hv
  simp only [Holds]
  refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_, h4.trans ?_, h5.trans ?_, h6.trans ?_,
    h7.trans ?_, h8.trans ?_, h9.trans ?_, h10.trans ?_, h11.trans ?_, h12.trans ?_,
    h13.trans ?_, h14.trans ?_, h15.trans ?_, h16.trans ?_, h17.trans ?_, h18.trans ?_,
    h19.trans ?_, h20.trans ?_, h21.trans ?_, h22.trans ?_, h23.trans ?_, h24.trans ?_,
    h25.trans ?_, h26.trans ?_, h27.trans ?_, h28.trans ?_, h29.trans ?_, h30.trans ?_,
    h31.trans ?_, h32.trans ?_, trivial⟩ <;>
    simp [Startup.valueOf, Startup.values, Prologue.abiFacts, Epilogue.ctaW, b32, List.lookup,
      e1, e2, e3, e4, e6, e7, e8]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
