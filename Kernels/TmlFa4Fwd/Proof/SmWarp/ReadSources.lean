-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.ReadPayloads
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataEvent
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src

@[expose] public section

/-! # The softmax warps' source premise from its rest

`SmWarp.SmSrc` asks that every event of a softmax lane returns what the fragment expects
(`Softmax.ExpectD`). At the scheduler's sites this follows from the scheduler's reference values
(`SmWarp.expectD_of`), so the premise reduces to its rest at the bias loads and the score loads
(`SmSrcRest`, `ExpectRest`): `goodRest` is `SmWarp.good` with the rest only, and
`smSrc_of_data_sites` derives the whole premise. The firing state's code invariant gives its
warp. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- **The rest of the softmax warps' source premise**: the bias loads' and the score loads'
returned values. -/
def SmSrcRest (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d n c e, X.get (g, k) = some e →
    Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.softmax,d⟩,n)) →
    Softmax.Ref p L g (d, c) → ExpectRest p L g d e

/-- The defined scheduler prefix supplies all other expectations of a live value state. -/
theorem smSrc_of_data_sites (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (_hN : NumAll p L) (hD : ∀ g, DataStoreSafe p L g) (hS : SmSrcRest p L X) : SmSrc p L X := by
  intro g k d n c e he hs hJ
  obtain ⟨hev, _, hw, _⟩ := data_event hp hX (hD g) he hs
  have hctl := control_of_data hp hs
  have hg := Frame.lt_of_get hX he
  have hF := (((good hp hX hw hg rfl k).2 _ hctl).2 (ub_zero hX he hctl)).2
  have hE := sexpect hp hX (cuQReadsFromLaunch hp hX) hg rfl he hctl hF hev.2
    (fun _ h j hin _ => good hp hX hw hin.1 hin.2 j)
  exact expectD_of hp hg hF hE (hS g k d n c e he hs hJ)

/-- The two data obligations follow from the values returned at the named PCs. -/
theorem smSrcRest_of_reads (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hr : ReadPayloads X) : SmSrcRest p L X :=
  fun _ _ _ _ _ _ he hst _ => expectRest_of_reads hp hX hr he hst

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
