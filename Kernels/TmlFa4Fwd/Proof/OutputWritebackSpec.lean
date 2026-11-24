-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Snoc.ControlEffect
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX Proof

noncomputable section

/-- One event site of the two-stage output writeback. `none` denotes its local exit. -/
inductive WritebackSite where
  | ready (stage : Fin 2)
  | store (stage : Fin 2) (subbox : Fin 4)
  | commit (stage : Fin 2)
  | readWait (stage : Fin 2)
  | release (stage : Fin 2)
  deriving DecidableEq

def writebackFreeLoc (l : Launch) (g : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (224 + 8 * stage.val)⟩

def writebackStoreSpec (p : Params) (l : Launch) (g batch head tile : Nat)
    (stage : Fin 2) (subbox : Fin 4) : TensorStore.Spec :=
  ⟨⟨3, p.oMap, oCoordinate p batch head (stageRow tile stage) (32 * subbox.val),
    sharedSlot l g stage subbox, none⟩, none⟩

section
variable {p : Params} {l : Launch}

/-- A wait carries its branch outcome in the event. Other events advance unconditionally. -/
def writebackSucceeded : Kind → Bool
  | .wait _ _ ok _ _ => ok
  | _ => true

end

variable {p : Params} {l : Launch}

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
