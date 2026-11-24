-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Open
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part115
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.DataStoreBytes
import Kernels.TmlFa4Fwd.Proof.Softmax.DataStoreSite
import Kernels.TmlFa4Fwd.Proof.Softmax.Safe
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The softmax data stores are no undefined behaviour

`dataStoreSafe`: the stores of data registers (the P stores, the statistics stores, the final
stores) have a supported, aligned address and four-byte values (`DataStoreSite.lean`,
`DataStoreBytes.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A register list within another, by evaluation. -/
private theorem sub_of_all {rs S : List Nat} (h : rs.all (S.contains ·) = true) :
    ∀ r ∈ rs, r ∈ S := fun r hr => List.contains_iff_mem.mp (List.all_eq_true.mp h r hr)

/-- A P store: its address register, its column address and its source registers. -/
macro "p_store" hp:ident d:term:max c:ident ta:term:max rs:term:max bytes:ident
    addr:term:max : tactic => `(tactic| (
  refine @tcSt_site _ _ _ _ $hp $d _ $ta $rs _ _ rfl $c rfl ?_
    ((valueOfD_ctl _ ?_).trans ?_) (ori_lt _ _) $addr ?_ ?_
  · kernel_rfl
  · kernel_rfl
  · soft_val'
  · rfl
  · exact fun r hr => $bytes $hp rfl (sub_of_all (by decide) r hr)))

private theorem safe_pst1 (hp : Pre p L m) (q : Fin 4) (v : V) (k : Fin 4) (acc : List Value) :
    (codeD p L g).ShapeAt NoUb ⟨.pst .first q, v, k, acc⟩ := by
  have ht := tmP_ok (g := g) hp
  match q with
  | 0 => p_store hp ⟨.pst .first 0, v, k, acc⟩
      Flow.code_4826 3223
      [3893, 3894, 3891, 3892, 3889, 3890, 3887, 3888, 3885, 3886, 3883, 3884, 3881,
       3882, 3879, 3880]
      bytes_p1 ht.1
  | 1 => p_store hp ⟨.pst .first 1, v, k, acc⟩
      Flow.code_4835 3226
      [3909, 3910, 3907, 3908, 3905, 3906, 3903, 3904, 3901, 3902, 3899, 3900, 3897,
       3898, 3895, 3896]
      bytes_p1 ht.2.1
  | 2 => p_store hp ⟨.pst .first 2, v, k, acc⟩
      Flow.code_4844 3225
      [3925, 3926, 3923, 3924, 3921, 3922, 3919, 3920, 3917, 3918, 3915, 3916, 3913,
       3914, 3911, 3912]
      bytes_p1 ht.2.2.1
  | 3 => p_store hp ⟨.pst .first 3, v, k, acc⟩
      Flow.code_4856 3224
      [3942, 3943, 3940, 3941, 3938, 3939, 3936, 3937, 3934, 3935, 3932, 3933, 3930,
       3931, 3928, 3929]
      bytes_p1 ht.2.2.2

private theorem safe_pstB (hp : Pre p L m) (q : Fin 4) (v : V) (k : Fin 4) (acc : List Value) :
    (codeD p L g).ShapeAt NoUb ⟨.pst .bias q, v, k, acc⟩ := by
  have ht := tmP_ok (g := g) hp
  match q with
  | 0 => p_store hp ⟨.pst .bias 0, v, k, acc⟩
      Flow.code_6508 4821
      [5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060,
       5061, 5062, 5063]
      bytes_pB ht.1
  | 1 => p_store hp ⟨.pst .bias 1, v, k, acc⟩
      Flow.code_6517 4824
      [5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076,
       5077, 5078, 5079]
      bytes_pB ht.2.1
  | 2 => p_store hp ⟨.pst .bias 2, v, k, acc⟩
      Flow.code_6526 4823
      [5080, 5081, 5082, 5083, 5084, 5085, 5086, 5087, 5088, 5089, 5090, 5091, 5092,
       5093, 5094, 5095]
      bytes_pB ht.2.2.1
  | 3 => p_store hp ⟨.pst .bias 3, v, k, acc⟩
      Flow.code_6541 4822
      [5099, 5100, 5101, 5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111,
       5112, 5113, 5114]
      bytes_pB ht.2.2.2

private theorem safe_pstP (hp : Pre p L m) (q : Fin 4) (v : V) (k : Fin 4) (acc : List Value) :
    (codeD p L g).ShapeAt NoUb ⟨.pst .plain q, v, k, acc⟩ := by
  have ht := tmP_ok (g := g) hp
  match q with
  | 0 => p_store hp ⟨.pst .plain 0, v, k, acc⟩
      Flow.code_7416 5183
      [5747, 5748, 5745, 5746, 5743, 5744, 5741, 5742, 5739, 5740, 5737, 5738, 5735,
       5736, 5733, 5734]
      bytes_pP ht.1
  | 1 => p_store hp ⟨.pst .plain 1, v, k, acc⟩
      Flow.code_7425 5185
      [5763, 5764, 5761, 5762, 5759, 5760, 5751, 5752, 5757, 5758, 5755, 5756, 5753,
       5754, 5749, 5750]
      bytes_pP ht.2.1
  | 2 => p_store hp ⟨.pst .plain 2, v, k, acc⟩
      Flow.code_7434 5181
      [5779, 5780, 5777, 5778, 5775, 5776, 5767, 5768, 5773, 5774, 5771, 5772, 5769,
       5770, 5765, 5766]
      bytes_pP ht.2.2.1
  | 3 => p_store hp ⟨.pst .plain 3, v, k, acc⟩
      Flow.code_7446 5184
      [5796, 5797, 5794, 5795, 5792, 5793, 5790, 5791, 5788, 5789, 5786, 5787, 5784,
       5785, 5782, 5783]
      bytes_pP ht.2.2.2

private theorem safe_stat (hp : Pre p L m) (b : Bool) (v : V) (k : Fin 4) (acc : List Value) :
    (codeD p L g).ShapeAt NoUb ⟨.stat b, v, k, acc⟩ := by
  have hA : ((statA L g).toNat + ((368 : Int) % 4).toNat) % 4 = 0 := by
    have := statA_al (g := g) hp; omega
  cases b
  · exact @st_site _ _ _ ⟨.stat false, v, k, acc⟩ _ 4571 1362 368 _ rfl
      Flow.code_5682 (fun _ _ h => h) (by kernel_rfl)
      ((valueOfD_ctl _ (by kernel_rfl)).trans (by soft_val')) hA (bytes_statB v k acc)
  · exact @st_site _ _ _ ⟨.stat true, v, k, acc⟩ _ 5518 1492 368 _ rfl
      Flow.code_6890 (fun _ _ h => h) (by kernel_rfl)
      ((valueOfD_ctl _ (by kernel_rfl)).trans (by soft_val')) hA (bytes_statP v k acc)

private theorem safe_fin (hp : Pre p L m) (j : Fin 2) (v : V) (k : Fin 4) (acc : List Value) :
    (codeD p L g).ShapeAt NoUb ⟨.fin j, v, k, acc⟩ := by
  have h4 := statA_al (g := g) hp
  match j with
  | 0 =>
    exact @st_site _ _ _ ⟨.fin 0, v, k, acc⟩ _ 5814 7257 368 _ rfl
      Flow.code_7614 (fun _ _ h => h) (by kernel_rfl)
      ((valueOfD_ctl _ (by kernel_rfl)).trans (by soft_val')) (by omega) (bytes_fin v k acc 0).1
  | 1 =>
    exact @st_site _ _ _ ⟨.fin 1, v, k, acc⟩ _ 5814 7256 1392 _ rfl
      Flow.code_7615 (fun _ _ h => h) (by kernel_rfl)
      ((valueOfD_ctl _ (by kernel_rfl)).trans (by soft_val')) (by omega) (bytes_fin v k acc 1).2

/-- **The softmax warps' data stores are no undefined behaviour.** -/
theorem dataStoreSafe (hp : Pre p L m) (g : Nat) : DataStoreSafe p L g := by
  rintro ⟨s, v, k, acc⟩ hd
  cases s with
  | pst r q =>
    cases r
    · exact safe_pst1 hp q v k acc
    · exact safe_pstB hp q v k acc
    · exact safe_pstP hp q v k acc
  | stat b => exact safe_stat hp b v k acc
  | fin j => exact safe_fin hp j v k acc
  | _ => simp [D.dataStore] at hd

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
