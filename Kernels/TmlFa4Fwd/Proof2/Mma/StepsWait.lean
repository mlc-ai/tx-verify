-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Mma.Base

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

set_option hygiene false in
/-- The poll of PV block 0 on a lane that issues no MMA: the walk to the next K slot's poll
passes the block's two guarded MMAs, then branches on the slot; the segment is cut after the
MMAs (`seg_auto`, then `seg_sym`). -/
theorem stepOk_mw0 (hp : Pre p L m) {v : V} : (code p L g ent).StepOk ⟨.mw 0 false, v⟩ := by
  have hparams := Epilogue.params hp
  refine' (PTX.Flow.Code.step_wait (dok := ⟨.wt 5, v⟩) (dfail := ⟨.mw 0 false, v⟩)
    ?hc ?hp ?hok ?hfail ?hs ?ha ?hlok ?hlfail)
  case hc => code_lookup
  case hs => rfl
  case ha => rfl
  case hp => fact_free
  case hok => intro m q a s; rfl
  case hfail => intro m q a s; rfl
  case hlfail =>
    refine ⟨fun _ => ?_, rfl, rfl, fun _ => trivial⟩
    site_norm
    seg_auto using ep_seg
  case hlok =>
    refine ⟨fun _ => ?_, rfl, rfl, fun _ => trivial⟩
    site_norm
    refine Seg.comp_ex (q := 2344)
      (H := Flow.factsFrom (Flow.live 2344) (valueOf p L g ent ⟨.mw 0 false, v⟩)) ?_ ?_
    · seg_auto using ep_seg
    · seg_sym using ep_seg

theorem stepAt_wait (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : (∃ k, d.site = .wt k) ∨ ∃ b l, d.site = .mw b l) :
    (code p L g ent).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨s, v⟩ := d
  mma_sites s except [.mw 0 false => (stepOk_mw0 hp)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Mma
