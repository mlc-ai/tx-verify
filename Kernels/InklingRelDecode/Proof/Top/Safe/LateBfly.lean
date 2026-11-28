-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.PWords
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Protocol.Values.ScratchWord
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Softmax.Export.SumWord
import Kernels.InklingRelDecode.Proof.Softmax.Export.BflyStages
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner

@[expose] public section

/-! # The words the `bfly` shuffles bring in are `.f32` data

The shuffles of the row maxima (pc 1838) send numbers or `-inf`, the row sum (pc 2234) a number,
the stages of the minimum butterfly the minimum of data, the decision shuffles (pcs 2253 and 2255)
the word read back from a scratch store of such a minimum. A lane receives the word its partner
sent at the same pc. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Flow.TyG Softmax.Export

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The words the `bfly` shuffles bring in, and the scratch word of pc 2252, are `.f32` data of
four bytes** (`Iface.LateValues.bfly`, `Iface.LateValues.ld`). -/
theorem Safe.bflyLd (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    (∀ {g k pc mode a b c recv ok}, X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩ →
      g % L.block < 128 → pc ∈ Iface.bflyPcs → Dat32 recv) ∧
    ∀ {g k a bs}, X.get (g, k) = some ⟨2252, .rd a bs⟩ → g % L.block < 128 →
      ∃ v, rebuild 3 bs = .ok v ∧ Dat32 v := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  have hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Softmax.Data.roundWords X g j,
      SK.ni.Has p.1 ∧ SK.ni.Has p.2 :=
    fun _ _ lane => Protocol.Shared.roundWords_ni hp hX hf hS lane
  have h5 : ∀ {g}, g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv :=
    fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf hS lane g1
  have agree : ∀ n, Protocol.Shared.StoreAgree L X n :=
    fun _ => Protocol.Shared.StoreAgree.of_safe hX safe
  have equal : Protocol.Shared.WarpStoresEqual L X :=
    Protocol.Shared.warp_stores_equal hp hX hf (Protocol.Shared.alpha_agree hp hX hf)
  have minDat : ∀ {x y}, Dat32 x → Dat32 y → Dat32 (Lib.minWord x y) := fun hx hy => by
    obtain ⟨v, hv, hdv⟩ := minE_total hx hy
    unfold Lib.minWord
    rw [hv]
    exact hdv
  have s53 : ∀ {g k mode a b c recv ok}, X.get (g, k) = some ⟨2253, .shfl mode a b c recv ok⟩ →
      Dat32 a := fun get => by
    obtain ⟨j, ac, bs, -, rd, ha, -⟩ := word_data hp hX get
    rw [ha]
    exact Protocol.Values.scratch_dat hp hX hf agree equal hR rd
  have r53 : ∀ {g k mode a b c recv ok}, X.get (g, k) = some ⟨2253, .shfl mode a b c recv ok⟩ →
      g % L.block < 128 → Dat32 recv := fun get lane => by
    obtain ⟨-, -, -, -, -, -, rfl, rfl, rfl⟩ := word_data hp hX get
    obtain ⟨j, b', c', r', o', got, low, -⟩ := late_partner hp hX hf get (by omega) (by omega) lane
    exact s53 got
  have stg : ∀ kk, kk ≤ 3 → ∀ {g k mode a b c recv ok},
      X.get (g, k) = some ⟨2242 + 2 * kk, .shfl mode a b c recv ok⟩ → g % L.block < 128 →
      Dat32 recv := fun kk hk {_ _ _ _ _ _ _ _} get lane => by
    obtain ⟨rfl, rfl, rfl⟩ := stage_shape hp hX hk get
    obtain ⟨-, d⟩ := stage_dat hp hX hf hR kk hk _ _ _ _ lane ⟨_, get⟩
    exact d
  refine ⟨?_, fun rd _ => Protocol.Values.scratch_rebuild hp hX hf agree equal hR rd⟩
  intro g k pc mode a b c recv ok get lane hpc
  simp only [Iface.bflyPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hr⟩ := Protocol.Shared.shfl5_ni hp hX hf hS lane get
    exact dat32_of_ni hr
  · obtain ⟨rfl, rfl, rfl, -⟩ := sent_sum hp hX hf (hS g) (@h5 g) get
    obtain ⟨j, b', c', r', o', got, low, -⟩ := late_partner hp hX hf get (by omega) (by omega) lane
    obtain ⟨-, -, -, hs⟩ := sent_sum hp hX hf (hS _) (@h5 _) got
    exact dat32_of_fl hs
  · exact (stg 0 (by omega) get lane)
  · exact (stg 1 (by omega) get lane)
  · exact (stg 2 (by omega) get lane)
  · exact (stg 3 (by omega) get lane)
  · exact (r53 get lane)
  · obtain ⟨rfl, rfl, rfl⟩ := shuffle_2255_shape hp hX get
    obtain ⟨j, ac, bs, p, ok1, rfl, rd, sh, -, -, -⟩ := rescale_data hp hX get
    obtain ⟨j', b', c', r', o', got, low, -⟩ := late_partner hp hX hf get (by omega) (by omega) lane
    obtain ⟨j2, ac2, bs2, p2, ok2, rfl, rd2, sh2, ha2, -, -⟩ := rescale_data hp hX got
    exact (ha2 ▸ minDat (Protocol.Values.scratch_dat hp hX hf agree equal hR rd2)
      (r53 sh2 low))


/-- **The words the `bfly` shuffles bring in are `.f32` data of four bytes.** -/
theorem Safe.bfly (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ {g k pc mode a b c recv ok}, X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩ →
      g % L.block < 128 → pc ∈ Iface.bflyPcs → Dat32 recv := by
  obtain ⟨h, -⟩ := Safe.bflyLd hp hX hf hou safe rows init nub
  exact h

/-- **The scratch word of pc 2252 is `.f32` data of four bytes.** -/
theorem Safe.ldWord (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ {g k a bs}, X.get (g, k) = some ⟨2252, .rd a bs⟩ → g % L.block < 128 →
      ∃ v, rebuild 3 bs = .ok v ∧ Dat32 v := by
  obtain ⟨-, h⟩ := Safe.bflyLd hp hX hf hou safe rows init nub
  exact h

end PTX.Kernels.InklingRelDecode.Proof.Top
