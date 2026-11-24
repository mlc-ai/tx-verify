-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionEvents

@[expose] public section

/-! # The correction warps' registers at their poll sites

The address and parity registers of each correction poll site (`oWait st`, `fWait st`,
`tailWait`), from the state's facts (`regv`). They are stated here, with the correction events'
imports only, so that the table lookups stay quick. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g i tt : Nat} {aw : Value} {a : ℝ} {o : List Value} {t : TState}

theorem regs_oWait0 (h : Holds t.regs (facts L g ⟨.oWait 0, i, tt, aw, a, o⟩)) :
    t.regs 3250 = some (b32 (sb L + 192)) ∧ t.regs 3937 = some (b32 (i % 2)) :=
  ⟨regv h 3250, regv h 3937⟩

theorem regs_oWait1 (h : Holds t.regs (facts L g ⟨.oWait 1, i, tt, aw, a, o⟩)) :
    t.regs 3252 = some (b32 (sb L + 200)) ∧ t.regs 3937 = some (b32 (i % 2)) :=
  ⟨regv h 3252, regv h 3937⟩

theorem regs_fWait0 (h : Holds t.regs (facts L g ⟨.fWait 0, i, tt, aw, a, o⟩)) :
    t.regs 3251 = some (b32 (sb L + 272)) ∧ t.regs 3939 = some (b32 ((i + 1) % 2)) :=
  ⟨regv h 3251, regv h 3939⟩

theorem regs_fWait1 (h : Holds t.regs (facts L g ⟨.fWait 1, i, tt, aw, a, o⟩)) :
    t.regs 3900 = some (b32 (sb L + 280)) ∧ t.regs 3939 = some (b32 ((i + 1) % 2)) :=
  ⟨regv h 3900, regv h 3939⟩

theorem regs_tailWait (h : Holds t.regs (facts L g ⟨.tailWait, i, tt, aw, a, o⟩)) :
    t.regs 3900 = some (b32 (sb L + 280)) ∧ t.regs 3939 = some (b32 ((i + 1) % 2)) :=
  ⟨regv h 3900, regv h 3939⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
