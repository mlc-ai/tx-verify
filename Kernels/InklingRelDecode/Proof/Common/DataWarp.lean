-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.ClsBuild
public import Kernels.InklingRelDecode.Proof.Common.DataCls
import Kernels.InklingRelDecode.Proof.Common.PreloadOrder
import Kernels.InklingRelDecode.Proof.Common.UbPrefix
import Kernels.InklingRelDecode.Proof.Lib.Rounds
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # The classification of a data warp

The collectives of the four data warps: the startup's shuffle, twelve elections, five collectives
for each preloaded block, the Softmax shuffles and the epilogue's (`dataCn`, `dataSlot`). -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem time_data {x} {σ : (thread Q L x).D} {p lim c : Nat} (h : DataCnt p lim σ c) :
    (schedule Q L).time x σ = stateClock σ := by
  obtain ⟨s, n⟩ := σ
  rcases s with st | ⟨r, d⟩
  · rfl
  rcases r with r | r
  · cases r with
    | dispatch => exact h.elim
    | prologue w =>
      rcases d with d | ⟨ent, d | ⟨u, d⟩⟩ <;> rfl
  · exact h.elim

/-- **The classification of the lanes of a data warp.** -/
theorem data_cls (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : g < L.threads) (lane : g % L.block < 128)
    (nu : ∀ x, SameWarp L g x → NoUbLane X x)
    (released : WarpRel Q L m X (SameWarp L g)) (dead : WarpDead Q L X (SameWarp L g)) :
    Sched.WarpCls (schedule Q L) m X (SameWarp L g) (CollAt Q L)
      (dataCn (Iface.preloadCount Q L (g / L.block)) (Lib.blocksOf Q L (g / L.block)))
      (dataSlot (Iface.preloadCount Q L (g / L.block)) (Lib.blocksOf Q L (g / L.block))) := by
  have hp3 := preload_le_three Q L (g / L.block)
  have hl := Lib.blocksOf_lt hp hg
  refine warpCls_of (F := fun x σ c => DataCnt (Iface.preloadCount Q L (g / L.block))
    (Lib.blocksOf Q L (g / L.block)) (σ : (thread Q L x).D) c) hp hX ?_ ?_ ?_ ?_ released dead
  · intro x σ c h
    obtain ⟨a, b, c'⟩ := data_state hp3 hl h
    have ca : CollAt Q L x σ ↔ isWarpAt (((schedule Q L).code x).pc σ) = true := collAt_iff_warp
    rw [time_data h]
    refine ⟨ca.trans a, fun w => b (ca.mp w), fun w n hn hle => c' ?_ n hn hle⟩
    cases e : isWarpAt (((schedule Q L).code x).pc σ)
    · exact e
    · exact absurd (ca.mpr e) w
  · intro x k σ hx hs
    obtain ⟨k', hk', hs', hc'⟩ := clip_state hs
    have hxt : x < L.threads := hx.1.2.1
    have hxl : x % L.block < 128 := by have := hx.2; omega
    have e : x / L.block = g / L.block := hx.1.2.2.symm
    have := data_cnt hp hX hf hxt hxl hk' (σ := σ) hs' ((nu x hx).before k')
    rw [e, hc'] at this
    exact this
  · intro a b hab hb
    exact data_slot_mono hp3 hl hab hb
  · intro x σ c h hpc
    exact data_exit h hpc

end PTX.Kernels.InklingRelDecode.Proof
