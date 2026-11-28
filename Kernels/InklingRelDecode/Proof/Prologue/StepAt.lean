-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Payload
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Sequence
import Kernels.InklingRelDecode.Proof.Prologue.Steps.InitElection
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Init
import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyElection
import Kernels.InklingRelDecode.Proof.Prologue.Steps.PreloadGate
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Barrier
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Arrive
import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockRead
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Copy
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Publish
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Store
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Shuffle
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

/-- Every event and vector substep of the prologue, through the softmax handoff. -/
theorem stepAt {m} (hp : Pre Q L m) (d : D) (pay : Payload d) : (code Q L g w).StepAtU d := by
  cases hs : d.site with
  | sMax => exact step_entry d hs
  | ld j =>
    fin_cases j
    · exact step_read_first d hs
    · exact step_read_last d hs
    · exact step_sequence hp d hs (pay.1 (by rw [hs]; decide))
  | el i => exact step_init_elect d i hs
  | init i => exact step_init d i hs
  | fnc0 => exact step_fence d (.inl hs)
  | bar2 => exact step_preload_gate hp d hs
  | pb b j =>
    fin_cases j
    · exact step_preload_head d b hs
    · exact step_preload_bar d b 0 hs
    · exact step_preload_bar d b 1 hs
    · exact step_preload_bar d b 2 hs
    · exact step_preload_bar d b 3 hs
  | arr b => exact step_arrive d b hs
  | lb b h => exact step_block_read d b h hs
  | psh b => exact step_shuffle d b hs
  | pel b j => exact step_copy_elect hp d b j hs
  | ptc b j =>
    by_cases inner : j.val<3
    · exact step_copy_inner d b ⟨j.val,inner⟩ hs
    · have eq : j=3 := Fin.ext (by change j.val=3; omega)
      subst j; exact step_issue_last hp d b hs
  | ldq j =>
    by_cases last : j.val%16=15
    · exact step_query_boundary d j hs last
    · exact step_query_inner j hs (by omega)
  | stq i j =>
    by_cases mid : j.val+1<4
    · exact step_store_mid d i j hs mid
    · have eq : j=3 := Fin.ext (by change j.val=3; omega)
      subst j; exact step_store_last d i hs
  | fnc1 => exact step_fence d (.inr hs)
  | st8 => exact step_role_word d hs
  | st9 j =>
    fin_cases j
    · exact step_pair_first d hs
    · exact step_pair_last d hs
  | bar18 => exact step_join d hs
  | exit => exact step_handoff d hs

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
