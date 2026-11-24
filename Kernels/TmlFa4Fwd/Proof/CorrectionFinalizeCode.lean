-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeWait
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputStores
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleNumerics
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow

noncomputable section

def finalizeDataBase (stage : Fin 2) (chunk : Fin 16) : Nat :=
  6516 + 280 * stage.val + 17 * chunk.val + min 7 (2 * chunk.val)

def finalizeDataRegs (stage : Fin 2) (chunk : Fin 16) : List Nat :=
  List.ofFn fun i : Fin 8 => finalizeDataBase stage chunk + i.val

def finalizePackBase (stage : Fin 2) (chunk : Fin 16) : Nat :=
  9260 + 132 * stage.val + 8 * chunk.val

def finalizeReciprocalPair (stage : Fin 2) : Nat := 9259 + 132 * stage.val

def finalizePacks (stage : Fin 2) (chunk : Fin 16) : List (Nat × Nat × Nat) :=
  let pack := finalizePackBase stage chunk
  let data := finalizeDataBase stage chunk
  (List.range 4).map fun i => (pack + i, data + (6 - 2 * i), data + (7 - 2 * i))

def finalizeMuls (stage : Fin 2) (chunk : Fin 16) : List (Nat × Nat) :=
  let pack := finalizePackBase stage chunk
  (List.range 4).map fun i => (pack + 4 + i, pack + (3 - i))

def finalizeSubset (chunk : Fin 16) : Fin 4 := ⟨chunk.val / 4, by omega⟩

def finalizeVector (chunk : Fin 16) (half : Fin 2) : Fin 8 :=
  ⟨2 * (chunk.val % 4) + half.val, by omega⟩

def finalizeUnpacks (stage : Fin 2) (chunk : Fin 16) (half : Fin 2) :
    List (Nat × Nat × Nat) :=
  let mul := finalizePackBase stage chunk + 4
  let left := 2 * half.val
  let word := outputStoreValueReg stage (finalizeSubset chunk) (finalizeVector chunk half)
  [(mul + left + 1, word 2, word 3), (mul + left, word 0, word 1)]

theorem finalizeRegisterCode (stage : Fin 2) (chunk : Fin 16) :
    kernel.code[finalizeLoadPc stage chunk]? = some
      ⟨none, .tcLd (finalizeDataRegs stage chunk) (finalizeAddressReg stage chunk) .s32x32b none⟩ :=
  by
    fin_cases stage <;> fin_cases chunk
    · exact Flow.code_8480
    · exact Flow.code_8499
    · exact Flow.code_8518
    · exact Flow.code_8537
    · exact Flow.code_8555
    · exact Flow.code_8572
    · exact Flow.code_8589
    · exact Flow.code_8606
    · exact Flow.code_8623
    · exact Flow.code_8640
    · exact Flow.code_8657
    · exact Flow.code_8674
    · exact Flow.code_8691
    · exact Flow.code_8708
    · exact Flow.code_8725
    · exact Flow.code_8742
    · exact Flow.code_8776
    · exact Flow.code_8795
    · exact Flow.code_8814
    · exact Flow.code_8833
    · exact Flow.code_8851
    · exact Flow.code_8868
    · exact Flow.code_8885
    · exact Flow.code_8902
    · exact Flow.code_8919
    · exact Flow.code_8936
    · exact Flow.code_8953
    · exact Flow.code_8970
    · exact Flow.code_8987
    · exact Flow.code_9004
    · exact Flow.code_9021
    · exact Flow.code_9038

theorem finalizePackCode (stage : Fin 2) (chunk : Fin 16) :
    PackCode kernel (finalizeLoadPc stage chunk + 1) (finalizePacks stage chunk) := by
  fin_cases stage <;> fin_cases chunk
  · exact ⟨Flow.code_8481, Flow.code_8482, Flow.code_8483, Flow.code_8484, trivial⟩
  · exact ⟨Flow.code_8500, Flow.code_8501, Flow.code_8502, Flow.code_8503, trivial⟩
  · exact ⟨Flow.code_8519, Flow.code_8520, Flow.code_8521, Flow.code_8522, trivial⟩
  · exact ⟨Flow.code_8538, Flow.code_8539, Flow.code_8540, Flow.code_8541, trivial⟩
  · exact ⟨Flow.code_8556, Flow.code_8557, Flow.code_8558, Flow.code_8559, trivial⟩
  · exact ⟨Flow.code_8573, Flow.code_8574, Flow.code_8575, Flow.code_8576, trivial⟩
  · exact ⟨Flow.code_8590, Flow.code_8591, Flow.code_8592, Flow.code_8593, trivial⟩
  · exact ⟨Flow.code_8607, Flow.code_8608, Flow.code_8609, Flow.code_8610, trivial⟩
  · exact ⟨Flow.code_8624, Flow.code_8625, Flow.code_8626, Flow.code_8627, trivial⟩
  · exact ⟨Flow.code_8641, Flow.code_8642, Flow.code_8643, Flow.code_8644, trivial⟩
  · exact ⟨Flow.code_8658, Flow.code_8659, Flow.code_8660, Flow.code_8661, trivial⟩
  · exact ⟨Flow.code_8675, Flow.code_8676, Flow.code_8677, Flow.code_8678, trivial⟩
  · exact ⟨Flow.code_8692, Flow.code_8693, Flow.code_8694, Flow.code_8695, trivial⟩
  · exact ⟨Flow.code_8709, Flow.code_8710, Flow.code_8711, Flow.code_8712, trivial⟩
  · exact ⟨Flow.code_8726, Flow.code_8727, Flow.code_8728, Flow.code_8729, trivial⟩
  · exact ⟨Flow.code_8743, Flow.code_8744, Flow.code_8745, Flow.code_8746, trivial⟩
  · exact ⟨Flow.code_8777, Flow.code_8778, Flow.code_8779, Flow.code_8780, trivial⟩
  · exact ⟨Flow.code_8796, Flow.code_8797, Flow.code_8798, Flow.code_8799, trivial⟩
  · exact ⟨Flow.code_8815, Flow.code_8816, Flow.code_8817, Flow.code_8818, trivial⟩
  · exact ⟨Flow.code_8834, Flow.code_8835, Flow.code_8836, Flow.code_8837, trivial⟩
  · exact ⟨Flow.code_8852, Flow.code_8853, Flow.code_8854, Flow.code_8855, trivial⟩
  · exact ⟨Flow.code_8869, Flow.code_8870, Flow.code_8871, Flow.code_8872, trivial⟩
  · exact ⟨Flow.code_8886, Flow.code_8887, Flow.code_8888, Flow.code_8889, trivial⟩
  · exact ⟨Flow.code_8903, Flow.code_8904, Flow.code_8905, Flow.code_8906, trivial⟩
  · exact ⟨Flow.code_8920, Flow.code_8921, Flow.code_8922, Flow.code_8923, trivial⟩
  · exact ⟨Flow.code_8937, Flow.code_8938, Flow.code_8939, Flow.code_8940, trivial⟩
  · exact ⟨Flow.code_8954, Flow.code_8955, Flow.code_8956, Flow.code_8957, trivial⟩
  · exact ⟨Flow.code_8971, Flow.code_8972, Flow.code_8973, Flow.code_8974, trivial⟩
  · exact ⟨Flow.code_8988, Flow.code_8989, Flow.code_8990, Flow.code_8991, trivial⟩
  · exact ⟨Flow.code_9005, Flow.code_9006, Flow.code_9007, Flow.code_9008, trivial⟩
  · exact ⟨Flow.code_9022, Flow.code_9023, Flow.code_9024, Flow.code_9025, trivial⟩
  · exact ⟨Flow.code_9039, Flow.code_9040, Flow.code_9041, Flow.code_9042, trivial⟩

theorem finalizeMulCode (stage : Fin 2) (chunk : Fin 16) :
    MulCodeE kernel .rn false (finalizeReciprocalPair stage)
      (finalizeLoadPc stage chunk + 6) (finalizeMuls stage chunk) := by
  fin_cases stage <;> fin_cases chunk
  · exact ⟨Flow.code_8486, Flow.code_8487, Flow.code_8488, Flow.code_8489, trivial⟩
  · exact ⟨Flow.code_8505, Flow.code_8506, Flow.code_8507, Flow.code_8508, trivial⟩
  · exact ⟨Flow.code_8524, Flow.code_8525, Flow.code_8526, Flow.code_8527, trivial⟩
  · exact ⟨Flow.code_8543, Flow.code_8544, Flow.code_8545, Flow.code_8546, trivial⟩
  · exact ⟨Flow.code_8561, Flow.code_8562, Flow.code_8563, Flow.code_8564, trivial⟩
  · exact ⟨Flow.code_8578, Flow.code_8579, Flow.code_8580, Flow.code_8581, trivial⟩
  · exact ⟨Flow.code_8595, Flow.code_8596, Flow.code_8597, Flow.code_8598, trivial⟩
  · exact ⟨Flow.code_8612, Flow.code_8613, Flow.code_8614, Flow.code_8615, trivial⟩
  · exact ⟨Flow.code_8629, Flow.code_8630, Flow.code_8631, Flow.code_8632, trivial⟩
  · exact ⟨Flow.code_8646, Flow.code_8647, Flow.code_8648, Flow.code_8649, trivial⟩
  · exact ⟨Flow.code_8663, Flow.code_8664, Flow.code_8665, Flow.code_8666, trivial⟩
  · exact ⟨Flow.code_8680, Flow.code_8681, Flow.code_8682, Flow.code_8683, trivial⟩
  · exact ⟨Flow.code_8697, Flow.code_8698, Flow.code_8699, Flow.code_8700, trivial⟩
  · exact ⟨Flow.code_8714, Flow.code_8715, Flow.code_8716, Flow.code_8717, trivial⟩
  · exact ⟨Flow.code_8731, Flow.code_8732, Flow.code_8733, Flow.code_8734, trivial⟩
  · exact ⟨Flow.code_8748, Flow.code_8749, Flow.code_8750, Flow.code_8751, trivial⟩
  · exact ⟨Flow.code_8782, Flow.code_8783, Flow.code_8784, Flow.code_8785, trivial⟩
  · exact ⟨Flow.code_8801, Flow.code_8802, Flow.code_8803, Flow.code_8804, trivial⟩
  · exact ⟨Flow.code_8820, Flow.code_8821, Flow.code_8822, Flow.code_8823, trivial⟩
  · exact ⟨Flow.code_8839, Flow.code_8840, Flow.code_8841, Flow.code_8842, trivial⟩
  · exact ⟨Flow.code_8857, Flow.code_8858, Flow.code_8859, Flow.code_8860, trivial⟩
  · exact ⟨Flow.code_8874, Flow.code_8875, Flow.code_8876, Flow.code_8877, trivial⟩
  · exact ⟨Flow.code_8891, Flow.code_8892, Flow.code_8893, Flow.code_8894, trivial⟩
  · exact ⟨Flow.code_8908, Flow.code_8909, Flow.code_8910, Flow.code_8911, trivial⟩
  · exact ⟨Flow.code_8925, Flow.code_8926, Flow.code_8927, Flow.code_8928, trivial⟩
  · exact ⟨Flow.code_8942, Flow.code_8943, Flow.code_8944, Flow.code_8945, trivial⟩
  · exact ⟨Flow.code_8959, Flow.code_8960, Flow.code_8961, Flow.code_8962, trivial⟩
  · exact ⟨Flow.code_8976, Flow.code_8977, Flow.code_8978, Flow.code_8979, trivial⟩
  · exact ⟨Flow.code_8993, Flow.code_8994, Flow.code_8995, Flow.code_8996, trivial⟩
  · exact ⟨Flow.code_9010, Flow.code_9011, Flow.code_9012, Flow.code_9013, trivial⟩
  · exact ⟨Flow.code_9027, Flow.code_9028, Flow.code_9029, Flow.code_9030, trivial⟩
  · exact ⟨Flow.code_9044, Flow.code_9045, Flow.code_9046, Flow.code_9047, trivial⟩

theorem finalizeUnpackCode (stage : Fin 2) (chunk : Fin 16) (half : Fin 2) :
    UnpackCode kernel
      (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half) - 2)
      (finalizeUnpacks stage chunk half) := by
  fin_cases stage <;> fin_cases chunk <;> fin_cases half
  · exact ⟨Flow.code_8490, Flow.code_8491, trivial⟩
  · exact ⟨Flow.code_8494, Flow.code_8495, trivial⟩
  · exact ⟨Flow.code_8509, Flow.code_8510, trivial⟩
  · exact ⟨Flow.code_8513, Flow.code_8514, trivial⟩
  · exact ⟨Flow.code_8528, Flow.code_8529, trivial⟩
  · exact ⟨Flow.code_8532, Flow.code_8533, trivial⟩
  · exact ⟨Flow.code_8547, Flow.code_8548, trivial⟩
  · exact ⟨Flow.code_8551, Flow.code_8552, trivial⟩
  · exact ⟨Flow.code_8565, Flow.code_8566, trivial⟩
  · exact ⟨Flow.code_8568, Flow.code_8569, trivial⟩
  · exact ⟨Flow.code_8582, Flow.code_8583, trivial⟩
  · exact ⟨Flow.code_8585, Flow.code_8586, trivial⟩
  · exact ⟨Flow.code_8599, Flow.code_8600, trivial⟩
  · exact ⟨Flow.code_8602, Flow.code_8603, trivial⟩
  · exact ⟨Flow.code_8616, Flow.code_8617, trivial⟩
  · exact ⟨Flow.code_8619, Flow.code_8620, trivial⟩
  · exact ⟨Flow.code_8633, Flow.code_8634, trivial⟩
  · exact ⟨Flow.code_8636, Flow.code_8637, trivial⟩
  · exact ⟨Flow.code_8650, Flow.code_8651, trivial⟩
  · exact ⟨Flow.code_8653, Flow.code_8654, trivial⟩
  · exact ⟨Flow.code_8667, Flow.code_8668, trivial⟩
  · exact ⟨Flow.code_8670, Flow.code_8671, trivial⟩
  · exact ⟨Flow.code_8684, Flow.code_8685, trivial⟩
  · exact ⟨Flow.code_8687, Flow.code_8688, trivial⟩
  · exact ⟨Flow.code_8701, Flow.code_8702, trivial⟩
  · exact ⟨Flow.code_8704, Flow.code_8705, trivial⟩
  · exact ⟨Flow.code_8718, Flow.code_8719, trivial⟩
  · exact ⟨Flow.code_8721, Flow.code_8722, trivial⟩
  · exact ⟨Flow.code_8735, Flow.code_8736, trivial⟩
  · exact ⟨Flow.code_8738, Flow.code_8739, trivial⟩
  · exact ⟨Flow.code_8752, Flow.code_8753, trivial⟩
  · exact ⟨Flow.code_8755, Flow.code_8756, trivial⟩
  · exact ⟨Flow.code_8786, Flow.code_8787, trivial⟩
  · exact ⟨Flow.code_8790, Flow.code_8791, trivial⟩
  · exact ⟨Flow.code_8805, Flow.code_8806, trivial⟩
  · exact ⟨Flow.code_8809, Flow.code_8810, trivial⟩
  · exact ⟨Flow.code_8824, Flow.code_8825, trivial⟩
  · exact ⟨Flow.code_8828, Flow.code_8829, trivial⟩
  · exact ⟨Flow.code_8843, Flow.code_8844, trivial⟩
  · exact ⟨Flow.code_8847, Flow.code_8848, trivial⟩
  · exact ⟨Flow.code_8861, Flow.code_8862, trivial⟩
  · exact ⟨Flow.code_8864, Flow.code_8865, trivial⟩
  · exact ⟨Flow.code_8878, Flow.code_8879, trivial⟩
  · exact ⟨Flow.code_8881, Flow.code_8882, trivial⟩
  · exact ⟨Flow.code_8895, Flow.code_8896, trivial⟩
  · exact ⟨Flow.code_8898, Flow.code_8899, trivial⟩
  · exact ⟨Flow.code_8912, Flow.code_8913, trivial⟩
  · exact ⟨Flow.code_8915, Flow.code_8916, trivial⟩
  · exact ⟨Flow.code_8929, Flow.code_8930, trivial⟩
  · exact ⟨Flow.code_8932, Flow.code_8933, trivial⟩
  · exact ⟨Flow.code_8946, Flow.code_8947, trivial⟩
  · exact ⟨Flow.code_8949, Flow.code_8950, trivial⟩
  · exact ⟨Flow.code_8963, Flow.code_8964, trivial⟩
  · exact ⟨Flow.code_8966, Flow.code_8967, trivial⟩
  · exact ⟨Flow.code_8980, Flow.code_8981, trivial⟩
  · exact ⟨Flow.code_8983, Flow.code_8984, trivial⟩
  · exact ⟨Flow.code_8997, Flow.code_8998, trivial⟩
  · exact ⟨Flow.code_9000, Flow.code_9001, trivial⟩
  · exact ⟨Flow.code_9014, Flow.code_9015, trivial⟩
  · exact ⟨Flow.code_9017, Flow.code_9018, trivial⟩
  · exact ⟨Flow.code_9031, Flow.code_9032, trivial⟩
  · exact ⟨Flow.code_9034, Flow.code_9035, trivial⟩
  · exact ⟨Flow.code_9048, Flow.code_9049, trivial⟩
  · exact ⟨Flow.code_9051, Flow.code_9052, trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
