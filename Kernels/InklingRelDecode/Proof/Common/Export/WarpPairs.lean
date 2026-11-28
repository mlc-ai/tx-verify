-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.WarpRel
public import Kernels.InklingRelDecode.Proof.Common.WarpColl
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
import Kernels.InklingRelDecode.Proof.Common.ClsBuild
import Kernels.InklingRelDecode.Proof.Common.DataWarp
import Kernels.InklingRelDecode.Proof.Common.IdleCls
import Kernels.InklingRelDecode.Proof.Common.LoaderState
import Kernels.InklingRelDecode.Proof.Common.MmaState
import all Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # The facts of two lanes of a warp, from the release facts of each warp's class -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The warp collectives of two lanes of any warp**, given that a released lane at a collective
releases its mates and that a stopped pending lane is released. -/
public theorem warp_pairs (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (nu : ∀ x, NoUbLane X x)
    (released : ∀ g, WarpRel Q L m X (SameWarp L g)) (dead : ∀ g, WarpDead Q L X (SameWarp L g))
    {g h : Nat} (hs : SameWarp L g h) :
    Sched.WarpPair m (schedule Q L) X (CollAt Q L) (collS Q L) g h := by
  have hg := hs.1.1
  have hS : ∀ {x y} {σ : ((schedule Q L).code x).D} {σ' : ((schedule Q L).code y).D},
      ((schedule Q L).code x).pc σ = ((schedule Q L).code y).pc σ' →
        collS Q L x σ = collS Q L y σ' :=
    fun e => by unfold collS; rw [e]
  have ht : Frame.Tracked (schedule Q L).code X := fun h k hh => (hf h hh k).1
  have hAg : SameWarp L g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  have hb : g % L.block < 256 := hp.block ▸ Nat.mod_lt _ (by rw [hp.block]; decide)
  by_cases hd : g % L.block < 128
  · exact Sched.warpPair_of_cls (data_cls hp hX hf hg hd (fun x _ => nu x) (released g) (dead g))
      hS ht hs hAg hs
  by_cases h6 : g % L.block / 32 = 6
  · exact Sched.warpPair_of_cls (loader_cls hp hX hf h6 (fun x _ => nu x) (released g) (dead g))
      hS ht hs hAg hs
  by_cases h7 : g % L.block / 32 = 7
  · exact Sched.warpPair_of_cls (mma_cls hp hX hf words h7 (fun x _ => nu x) (released g) (dead g))
      hS ht hs hAg hs
  exact Sched.warpPair_of_cls (idle_cls hp hX hf h6 h7 (by omega) (fun x _ => nu x) (released g)
    (dead g)) hS ht hs hAg hs

end PTX.Kernels.InklingRelDecode.Proof.Export
