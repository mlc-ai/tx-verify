-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueWarp0

@[expose] public section

/-! # The events of the prologue's sites

Each prologue site fires one event of its kind: a shuffle, an election, a barrier
initialization, a fence or a cluster-barrier operation. An initialization names its barrier and
count: `init j` initializes `FBar.ofInit j` and `init320` the handshake barrier, each in the
thread's own CTA and with the table's count (`init_event`, `init320_event`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g w rk : Nat} {t u : TState} {e : Event}
  {ins : Instr}

/-- A shared mbarrier address: a 32-bit register and an offset. -/
theorem mbarLoc_off {base a off : Nat} (hb : t.regs base = some (b32 a)) (ha : a + off < 2 ^ 32)
    (h8 : (a + off) % 8 = 0) :
    mbarLoc L g t base (off : Int) = .ok ⟨.shared, g / L.block, a + off⟩ := by
  have h : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) + BitVec.ofNat 64 off)).toNat =
      a + off := by
    norm_bits
  simp [mbarLoc, effAddr, sharedEffAddr, readReg, hb, b32, readBits, bind, Except.bind,
    pure, Except.pure]
  simp [h, h8]

/-- An `mbarrier.init` addressed by a 32-bit register and an offset, with its count from a
register, fires the initialization of the thread's own CTA's barrier at that address. -/
theorem fires_mbarInit_reg {A : List Assumption} {pc base rc a n off : Nat} {o : Option TState}
    (hb : t.regs base = some (b32 a)) (hc : t.regs rc = some (b32 n)) (ha : a + off < 2 ^ 32)
    (h8 : (a + off) % 8 = 0) (hn : 0 < n) (hn' : n < 2 ^ 20)
    (hf : Fires pc (eventTmpl A L g t (.mbarInit base off (.reg rc))) e o) :
    e = ⟨pc, .mbInit ⟨.shared, g / L.block, a + off⟩ n⟩ := by
  have hr : (truncBits 32 (BitVec.ofNat 64 n)).toNat = n := by norm_bits
  have hrd : readBits L g t 32 (.reg rc) = .ok (truncBits 32 (BitVec.ofNat 64 n)) := by
    simp [readBits, readReg, hc, b32, bind, Except.bind, pure, Except.pure]
  simp only [eventTmpl, tmaTmpl, mbarLoc_off hb ha h8, hrd, hr, bind, Except.bind] at hf
  simp only [show 0 < n ∧ n < 2 ^ 20 from ⟨hn, hn'⟩, pure, Except.pure, ofExec,
    widenMbarScope] at hf
  split at hf <;> exact hf.1

/-- A prologue initialization: the barrier above the shared base named by the table. -/
theorem init_fire {A : List Assumption} {pc base rc off c n : Nat} {o : Option TState}
    (hpre : Pre P L mem0) (h : At t pc (factsAt L g w rk pc)) (hbl : base ∈ Flow.live pc)
    (hcl : rc ∈ Flow.live pc) (hbv : valueOf L g w rk base = b32 (L.sharedBase + c))
    (hcv : valueOf L g w rk rc = b32 n) (hn : 0 < n ∧ n < 2 ^ 20) (h8 : (c + off) % 8 = 0)
    (hlt : c + off < 328) (hf : Fires pc (eventTmpl A L g t (.mbarInit base off (.reg rc))) e o) :
    e = ⟨pc, .mbInit ⟨.shared, ctaOf L g, L.sharedBase + (c + off)⟩ n⟩ := by
  have hb := hbv ▸ holds_mem h.2.2.2.2 (mem_factsFrom hbl)
  have hc := hcv ▸ holds_mem h.2.2.2.2 (mem_factsFrom hcl)
  have hal := hpre.sharedAlignment
  have hr := hpre.sharedRange
  unfold sharedBytes at hr
  rw [fires_mbarInit_reg hb hc (by omega) (by omega) hn.1 hn.2 hf, Nat.add_assoc]
  rfl

/-- Warp 0's initialization `j` initializes barrier `FBar.ofInit j` of the thread's CTA with its
count. -/
theorem init_event {A : List Assumption} {o : Option TState} (hpre : Pre P L mem0) (j : Fin 36)
    (h : At t (Site.init j).pc (factsAt L g w rk (Site.init j).pc))
    (hc : kernel.code[(Site.init j).pc]? = some ins)
    (hf : Fires (Site.init j).pc (eventTmpl A L g t ins.op) e o) :
    e = ⟨(Site.init j).pc,
      .mbInit (FBar.loc L (ctaOf L g) (FBar.ofInit j)) (FBar.ofInit j).count⟩ := by
  fin_cases j
  all_goals
    code_at hc
    subst hc
    rw [init_fire hpre h (by table_decide) (by table_decide) (by pro_values; rfl)
      (by pro_values; rfl) (by decide) (by decide) (by decide) hf]
    rfl

/-- Warp 12's initialization of the handshake barrier. -/
theorem init320_event {A : List Assumption} {o : Option TState} (hpre : Pre P L mem0)
    (h : At t Site.init320.pc (factsAt L g w rk Site.init320.pc))
    (hc : kernel.code[Site.init320.pc]? = some ins)
    (hf : Fires Site.init320.pc (eventTmpl A L g t ins.op) e o) :
    e = ⟨Site.init320.pc, .mbInit (FBar.loc L (ctaOf L g) .dealloc) FBar.dealloc.count⟩ := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_0)
  rw [init_fire (off := 0) hpre h (by table_decide) (by table_decide) (by pro_values; rfl)
    (by pro_values; rfl) (by decide) (by decide) (by decide) hf]
  rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
