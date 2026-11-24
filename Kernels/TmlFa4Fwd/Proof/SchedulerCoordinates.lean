-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
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
public import Lemmas.Flow.Scalars
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

def sectionHead (tiles width work : Nat) : Nat := work / (width * tiles) * width

theorem sectionHead_lt {tiles heads width work : Nat} (hWork : work < tiles * heads) :
    sectionHead tiles width work < heads := by
  have hu := Nat.div_mul_le_self work (width * tiles)
  have hc : sectionHead tiles width work * tiles ≤ work := by
    simpa only [sectionHead, Nat.mul_assoc] using hu
  by_contra! h
  have H := Nat.mul_le_mul_right tiles h
  rw [Nat.mul_comm heads] at H
  omega

def sectionStride (tiles heads width work : Nat) : Nat :=
  min width (heads - sectionHead tiles width work)

/-- The request-relative section mapping implemented by the scalar scheduler. -/
def assignedCoordinates (p : Params) (batch item : Nat) : Nat × Nat :=
  sectionCoords (requestTiles p batch) p.heads (sectionWidth (requestTiles p batch) p.heads)
    (item - tilePrefix p batch * p.heads)

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
