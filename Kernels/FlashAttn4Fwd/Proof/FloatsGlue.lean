-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.HasUb
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsLoad
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsStats
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsShfl

@[expose] public section

/-! # The value premises of the undefined-behaviour branch

`LoadFloats`, `StatsFloats` and `ShflUniform`, from the value protocols (`Floats.load_floats`,
`Floats.stats_floats`, `Floats.shfl_own`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every Tensor Memory load returns single-precision floats.** -/
theorem loadFloats (hX : Consistent L kernel asms mem0 X) (ht : ScoreFacts L X)
    (hf : FloatFacts L X) (hs : Floats.LoadSources L X) : LoadFloats L X :=
  fun hg he => Floats.load_floats hX ht hf hs hg he

/-- **Every correction `ld.shared` returns the bytes of a single-precision float**, when every
softmax thread's Tensor Memory load returns single-precision floats (`hsl`). -/
theorem statsFloats (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : StatsFacts L X) (hf : FloatFacts L X) (htm : TmemFacts L X) (hU : Stats.StatsCredit L X)
    (hsoft : Stats.SoftArrives L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStatsArea L l → False)
    (hsl : ∀ {g k pc a : Nat} {vals : List Value}, g < L.threads → warpOf L g < 8 →
      X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩ → F32s vals) :
    StatsFloats L X :=
  fun hg h8 h12 he => Floats.stats_floats hpre hX ht hf htm hU hsoft hasync hg h8 h12 he
    fun hg' hw _ _ _ _ _ _ _ _ hld => hsl hg' hw hld

/-- **Every shuffle returns its own source value.** -/
theorem shflUniform (hX : Consistent L kernel asms mem0 X) (hf : FloatFacts L X) :
    ShflUniform L X :=
  fun hg he => Floats.shfl_own hX hf hg he

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
