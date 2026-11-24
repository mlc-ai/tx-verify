-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0Facts

@[expose] public section

/-! # The first tile's row maximum: the reads from `1341` -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem segMax0_1341 {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 111 1341
      (factsFrom (Flow.live 1341)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1341 L d))) 1452
      (factsFrom (Flow.live 1452)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1452 L d ++ (exMax0_1341 L d))))
      (rCond (valueEx (valueOf L g { d with site := .ldW false 3 }) (exMax0_1341 L d))
        readsMax0_1341) := by
  refine SegD.reads (pc := 1341) (keys :=
      [1009, 1232, 1237, 1239, 1243, 1245, 1249, 1251, 1255, 1257, 1261, 1263, 1267, 1269, 1273,
       1275, 1279, 1281, 1285, 1287, 1291, 1293, 1297, 1299, 1303, 1305, 1309, 1311, 1315, 1317,
       1321, 1323, 1327, 1328, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999,
       4000, 4001, 4002, 4003, 4004])
    (by decide +kernel) (by decide +kernel) (by kernel_rfl)
    (by decide +kernel) (noItemRule_asms _) (segFree_asms (by decide +kernel))
    (ideal_max_range (by decide +kernel)) (decline_max_range (by decide +kernel)) (by kernel_rfl)
    rfl (by decide +kernel) (by decide +kernel)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
