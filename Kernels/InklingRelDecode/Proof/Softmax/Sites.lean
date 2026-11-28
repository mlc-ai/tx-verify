-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Flow.Sites.Part000
public import Lemmas.Flow.Roles
public import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow

inductive Site where
  /-- Region A: the register increase, the named barrier, the 64 preloads of the first block's
  bias, then the loop's own bias loads. -/
  | setMaxReg | bar0
  | pre (j : Fin 64)
  | nxt (j : Fin 64)
  /-- Region B: the `s_ready` poll, the broadcast of the warp index, the S tile's `tcgen05.ld`
  and its wait. -/
  | waitS | shfl4 | ldS | waitLd
  /-- Region C: the two row shuffles that bound the score, maximum, exponential and sum code. -/
  | shfl5 | shfl6
  /-- Region D: the remaining shuffle exchanges, the row sum's shared store, its reload, the
  `o_done` poll, the O rescale and the P store with its `p_ready` arrival. -/
  | bar22 | shfl7 | shfl8 | shfl9 | shfl10 | store10 | bar23 | ldL | shfl11 | shfl12
  | waitO | ldO | waitLdO | bar24 | stO | waitStO
  | bar20 | tmemSt | tmemWait | bar21 | arrive
  | epilogue
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_1 | .bar0 => Flow.bar_19
  | .pre j => 680 + 2 * j.val
  | .nxt j => 1124 + 2 * j.val
  | .waitS => Flow.mbarWait_0 | .shfl4 => Flow.shfl_4 | .ldS => Flow.tmemLoad_0
  | .waitLd => Flow.tmemWait_1
  | .shfl5 => Flow.shfl_5 | .shfl6 => Flow.shfl_6
  | .bar22 => Flow.bar_22 | .shfl7 => Flow.shfl_7 | .shfl8 => Flow.shfl_8
  | .shfl9 => Flow.shfl_9 | .shfl10 => Flow.shfl_10 | .store10 => Flow.store_10
  | .bar23 => Flow.bar_23 | .ldL => Flow.load_202 | .shfl11 => Flow.shfl_11
  | .shfl12 => Flow.shfl_12
  | .waitO => Flow.mbarWait_1 | .ldO => Flow.tmemLoad_1 | .waitLdO => Flow.tmemWait_2
  | .bar24 => Flow.bar_24 | .stO => Flow.tmemStore_1 | .waitStO => Flow.tmemWait_3
  | .bar20 => Flow.bar_20 | .tmemSt => Flow.tmemStore_0 | .tmemWait => Flow.tmemWait_0
  | .bar21 => Flow.bar_21 | .arrive => Flow.mbarArrive_3

  | .epilogue => 2565

/-- Decoded instruction order includes the backward branch into the P-store block,
and the first epilogue poll as the hand-off site. -/
def allSites : List Site :=
  [.setMaxReg,.bar0] ++ (List.finRange 64).map Site.pre ++
  [.bar20,.tmemSt,.tmemWait,.bar21,.arrive] ++ (List.finRange 64).map Site.nxt ++
  [.waitS,.shfl4,.ldS,.waitLd,.shfl5,.shfl6,.waitO,.bar22,.shfl7,.shfl8,.shfl9,.shfl10,
   .store10,.bar23,.ldL,.shfl11,.shfl12,.ldO,.waitLdO,.bar24,.stO,.waitStO,.epilogue]

def region : RoleDecl := ⟨[(574,2331),(2560,2566)],[2565]⟩

theorem sites_pcs : allSites.map Site.pc = RoleDecl.sites kernel region := by kernel_rfl

theorem sites_nodup : (allSites.map Site.pc).Nodup := by decide +kernel

theorem Site.pc_range (s : Site) : (574 ≤ s.pc ∧ s.pc < 2331) ∨ s = .epilogue := by
  cases s <;> first | exact .inl (by decide) | exact .inr rfl |
    (rename_i j; left; change 574 ≤ _ + 2*j.val ∧ _ + 2*j.val < 2331; omega)

end PTX.Kernels.InklingRelDecode.Proof.Softmax
