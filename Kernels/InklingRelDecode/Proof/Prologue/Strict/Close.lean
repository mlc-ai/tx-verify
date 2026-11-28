-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.PreStepC
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QStqStep
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QLdStep
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Ld3

@[expose] public section

/-! # The strict step of every site of the prologue

`step_site` dispatches on the site; the exit has none (a glued machine leaves the prologue at the
exit, so it never holds a state there). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- **Every state of the prologue but the exit steps strictly.** -/
theorem step_site {m} (hp : Pre Q L m) (hg : g < L.threads) (hw0 : w = b32 0) (d : Data.D)
    (hs : d.c.site ≠ .exit) (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, y, p, won, bcast⟩, vs⟩ := d
  cases s with
  | sMax => exact step_sMax _ rfl e
  | ld k =>
    fin_cases k
    · exact step_ld0 _ rfl e
    · exact step_ld1 _ rfl hk e
    · exact step_ld2 hp hg _ rfl hk e
  | el i => exact step_el _ i rfl hk e
  | init i => exact step_init _ i rfl e
  | fnc0 => exact step_fnc0 _ rfl e
  | bar2 => exact step_bar2 hp hg hw0 _ rfl hk e
  | pb b j =>
    fin_cases j
    · exact step_pb0 _ b rfl e
    · exact step_pbT _ b 0 rfl e
    · exact step_pbT _ b 1 rfl e
    · exact step_pbT _ b 2 rfl e
    · exact step_pbT _ b 3 rfl e
  | arr b => exact step_arr _ b rfl e
  | lb b h => exact step_lb _ b h rfl e
  | psh b => exact step_psh _ b rfl e
  | pel b j => exact step_pel hp hw0 _ b j rfl hk e
  | ptc b j => exact step_ptc hp hw0 _ b j rfl hk e
  | ldq k => exact step_ldq _ k rfl hk e
  | stq i j => exact step_stq _ i j rfl hk e
  | fnc1 => exact step_fnc1 _ rfl e
  | st8 => exact step_st8 _ rfl e
  | st9 j => exact step_st9 _ j rfl e
  | bar18 => exact step_bar18 _ rfl e
  | exit => exact absurd rfl hs

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
