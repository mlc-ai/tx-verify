-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Data
public import Kernels.TmlFa4Fwd.Proof2.Startup.Machine

@[expose] public section

/-! # The softmax warps' first state and its hand-off from the startup

The fragment of warps 0 to 7 for lane T1's glue (`Proof2/Common`) is the softmax machine
`code p L g` from the role's entry, the `setmaxnreg` at pc 3102 (it has no `ent` argument: the
registers live there that the role never writes have their startup values in `valuesStart`). The
facts of its first state are an explicit list over the registers live at pc 3102, all of them
control registers (`facts_init`): the warp index, the CTA index, the shared base and four
shared-memory barrier addresses, the batch, and the LSE and request pointers.

The hand-off (`handoff`): a thread state that holds the startup's facts at `enter softmax`, with
the shared base `x1 = sharedBase` and the warp word `x3 = g % L.block / 32` that the role's gate
fixes, holds the fragment's first facts. The lemmas on the startup's words (`addi_sb`, `cta_word`,
`batch_word`) are local copies of `Common/Sound.lean`'s, since this directory may not import lane
T1's files (the loader's `Handoff.lean` does the same). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem live_3102 : Flow.live 3102 =
    [1062, 1069, 1072, 2390, 2535, 6495, 6497, 7247, 7500, 7501, 7502, 7503, 7506] := by
  rfl

theorem ctlLive_3102 : ctlLive 3102 =
    [1062, 1069, 1072, 2390, 2535, 6495, 6497, 7247, 7500, 7501, 7502, 7503, 7506] := by
  rw [ctlLive, live_3102]; decide

theorem liveD_3102 : liveD 3102 =
    [1062, 1069, 1072, 2390, 2535, 6495, 6497, 7247, 7500, 7501, 7502, 7503, 7506] := by
  rw [liveD, live_3102]; decide

/-- **The facts of the softmax machine's first state.** -/
theorem facts_init (p : Params) (L : Launch) (g : Nat) :
    (codeD p L g).facts (codeD p L g).init =
      [(1062, b32 (g % L.block / 32)), (1069, b32 (L.sharedBase + 192)),
       (1072, .bits 32 (Epilogue.ctaW L g)), (2390, b32 (L.sharedBase + 208)),
       (2535, b32 L.sharedBase), (6495, b32 (L.sharedBase + 144)),
       (6497, b32 (L.sharedBase + 224)), (7247, b32 p.batch), (7500, b64 p.lseBase),
       (7501, b64 p.lseStride), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
       (7506, b64 p.cuQBase)] := by
  show Flow.factsFrom (liveD (livePc (D.mk' .setmax {}))) _ = _
  rw [show livePc (D.mk' .setmax {}) = 3102 from rfl, liveD_3102]
  rfl

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

/-- **The hand-off from the startup**: a thread state with the startup's facts at `enter softmax`,
whose shared base and warp word are the gate's, holds the facts of the fragment's first state. -/
theorem handoff (hp : Pre p L m) (hg : g < L.threads) {t : TState} {x2 : BitVec 64}
    (hF : Holds t.regs (Startup.facts p L g
      ⟨.enter .softmax, BitVec.ofNat 64 L.sharedBase, x2, BitVec.ofNat 64 (g % L.block / 32)⟩)) :
    Holds t.regs ((codeD p L g).facts (codeD p L g).init) := by
  rw [facts_init]
  have hb := hp.shared.2.1
  have e1 := addi_sb (b := L.sharedBase) (n := 192) (by omega)
  have e2 := addi_sb (b := L.sharedBase) (n := 208) (by omega)
  have e3 := addi_sb (b := L.sharedBase) (n := 144) (by omega)
  have e4 := addi_sb (b := L.sharedBase) (n := 224) (by omega)
  simp only [Nat.cast_ofNat] at e1 e2 e3 e4
  have e6 := cta_word hp hg
  have e7 := batch_word hp
  have hv : ∀ r ∈ Flow.live 3102, t.regs r = some (Startup.valueOf p L g
      ⟨.enter .softmax, BitVec.ofNat 64 L.sharedBase, x2, BitVec.ofNat 64 (g % L.block / 32)⟩ r) :=
    fun r hr => holds_mem hF (mem_factsFrom hr)
  simp only [live_3102, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hv
  simp only [Holds]
  refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_, h4.trans ?_, h5.trans ?_, h6.trans ?_,
    h7.trans ?_, h8.trans ?_, h9.trans ?_, h10.trans ?_, h11.trans ?_, h12.trans ?_,
    h13.trans ?_, trivial⟩ <;>
    simp [Startup.valueOf, Startup.values, Prologue.abiFacts, Epilogue.ctaW, b32, List.lookup,
      e1, e2, e3, e4, e6, e7]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
