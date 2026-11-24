-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemStores
public import Kernels.TmlFa4Fwd.Proof.CorrectionStats
public import Lemmas.Flow.MulPairCore
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow

noncomputable section

def rescaleDataBase (stage : Fin 2) (chunk : Fin 8) : Nat :=
  5980 + 258 * stage.val + 32 * chunk.val

def rescalePackBase (stage : Fin 2) (chunk : Fin 8) : Nat :=
  8995 + 131 * stage.val + 16 * chunk.val + if chunk.val = 0 then 0 else 1

def rescaleAlphaPair (stage : Fin 2) : Nat := 9003 + 131 * stage.val

def rescalePacks (stage : Fin 2) (chunk : Fin 8) : List (Nat × Nat × Nat) :=
  let pack := rescalePackBase stage chunk
  let data := rescaleDataBase stage chunk
  ((List.range 8).map fun k => (pack + k, data + (14 - 2 * k), data + (15 - 2 * k))) ++
    if chunk.val = 0 then
      [(rescaleAlphaPair stage, statsReg stage .alpha, statsReg stage .alpha)]
    else []

def rescaleMulBase (stage : Fin 2) (chunk : Fin 8) : Nat :=
  rescalePackBase stage chunk + (rescalePacks stage chunk).length

def rescaleMuls (stage : Fin 2) (chunk : Fin 8) : List (Nat × Nat) :=
  (List.range 8).map fun k =>
    (rescaleMulBase stage chunk + k, rescalePackBase stage chunk + (7 - k))

def rescaleUnpacks (stage : Fin 2) (chunk : Fin 8) : List (Nat × Nat × Nat) :=
  (List.range 8).map fun k =>
    (rescaleMulBase stage chunk + (7 - k), rescaleDataBase stage chunk + 16 + 2 * k,
      rescaleDataBase stage chunk + 17 + 2 * k)

/-- A rescale load writes sixteen consecutive accumulator registers. -/
def rescaleDataRegs (stage : Fin 2) (chunk : Fin 8) : List Nat :=
  List.ofFn fun i : Fin 16 => rescaleDataBase stage chunk + i.val

theorem rescaleRegisterCode (stage : Fin 2) (chunk : Fin 8) :
    kernel.code[rescaleLoadPc stage chunk]? = some
      ⟨none, .tcLd (rescaleDataRegs stage chunk) (rescaleAddressReg stage chunk) .s32x32b none⟩ :=
  by
    fin_cases stage <;> fin_cases chunk
    · exact Flow.code_8012
    · exact Flow.code_8039
    · exact Flow.code_8065
    · exact Flow.code_8091
    · exact Flow.code_8117
    · exact Flow.code_8143
    · exact Flow.code_8169
    · exact Flow.code_8195
    · exact Flow.code_8231
    · exact Flow.code_8258
    · exact Flow.code_8284
    · exact Flow.code_8310
    · exact Flow.code_8336
    · exact Flow.code_8362
    · exact Flow.code_8388
    · exact Flow.code_8414

theorem rescalePackCode (stage : Fin 2) (chunk : Fin 8) :
    PackCode kernel (rescaleLoadPc stage chunk + 1) (rescalePacks stage chunk) := by
  fin_cases stage <;> fin_cases chunk
  · exact ⟨Flow.code_8013, Flow.code_8014, Flow.code_8015, Flow.code_8016,
      Flow.code_8017, Flow.code_8018, Flow.code_8019, Flow.code_8020,
      Flow.code_8021, trivial⟩
  · exact ⟨Flow.code_8040, Flow.code_8041, Flow.code_8042, Flow.code_8043,
      Flow.code_8044, Flow.code_8045, Flow.code_8046, Flow.code_8047,
      trivial⟩
  · exact ⟨Flow.code_8066, Flow.code_8067, Flow.code_8068, Flow.code_8069,
      Flow.code_8070, Flow.code_8071, Flow.code_8072, Flow.code_8073,
      trivial⟩
  · exact ⟨Flow.code_8092, Flow.code_8093, Flow.code_8094, Flow.code_8095,
      Flow.code_8096, Flow.code_8097, Flow.code_8098, Flow.code_8099,
      trivial⟩
  · exact ⟨Flow.code_8118, Flow.code_8119, Flow.code_8120, Flow.code_8121,
      Flow.code_8122, Flow.code_8123, Flow.code_8124, Flow.code_8125,
      trivial⟩
  · exact ⟨Flow.code_8144, Flow.code_8145, Flow.code_8146, Flow.code_8147,
      Flow.code_8148, Flow.code_8149, Flow.code_8150, Flow.code_8151,
      trivial⟩
  · exact ⟨Flow.code_8170, Flow.code_8171, Flow.code_8172, Flow.code_8173,
      Flow.code_8174, Flow.code_8175, Flow.code_8176, Flow.code_8177,
      trivial⟩
  · exact ⟨Flow.code_8196, Flow.code_8197, Flow.code_8198, Flow.code_8199,
      Flow.code_8200, Flow.code_8201, Flow.code_8202, Flow.code_8203,
      trivial⟩
  · exact ⟨Flow.code_8232, Flow.code_8233, Flow.code_8234, Flow.code_8235,
      Flow.code_8236, Flow.code_8237, Flow.code_8238, Flow.code_8239,
      Flow.code_8240, trivial⟩
  · exact ⟨Flow.code_8259, Flow.code_8260, Flow.code_8261, Flow.code_8262,
      Flow.code_8263, Flow.code_8264, Flow.code_8265, Flow.code_8266,
      trivial⟩
  · exact ⟨Flow.code_8285, Flow.code_8286, Flow.code_8287, Flow.code_8288,
      Flow.code_8289, Flow.code_8290, Flow.code_8291, Flow.code_8292,
      trivial⟩
  · exact ⟨Flow.code_8311, Flow.code_8312, Flow.code_8313, Flow.code_8314,
      Flow.code_8315, Flow.code_8316, Flow.code_8317, Flow.code_8318,
      trivial⟩
  · exact ⟨Flow.code_8337, Flow.code_8338, Flow.code_8339, Flow.code_8340,
      Flow.code_8341, Flow.code_8342, Flow.code_8343, Flow.code_8344,
      trivial⟩
  · exact ⟨Flow.code_8363, Flow.code_8364, Flow.code_8365, Flow.code_8366,
      Flow.code_8367, Flow.code_8368, Flow.code_8369, Flow.code_8370,
      trivial⟩
  · exact ⟨Flow.code_8389, Flow.code_8390, Flow.code_8391, Flow.code_8392,
      Flow.code_8393, Flow.code_8394, Flow.code_8395, Flow.code_8396,
      trivial⟩
  · exact ⟨Flow.code_8415, Flow.code_8416, Flow.code_8417, Flow.code_8418,
      Flow.code_8419, Flow.code_8420, Flow.code_8421, Flow.code_8422,
      trivial⟩

theorem rescaleMulCode (stage : Fin 2) (chunk : Fin 8) :
    MulCodeE kernel .rn false (rescaleAlphaPair stage)
      (rescaleLoadPc stage chunk + 1 + (rescalePacks stage chunk).length)
      (rescaleMuls stage chunk) := by
  fin_cases stage <;> fin_cases chunk
  · exact ⟨Flow.code_8022, Flow.code_8023, Flow.code_8024, Flow.code_8025,
      Flow.code_8026, Flow.code_8027, Flow.code_8028, Flow.code_8029,
      trivial⟩
  · exact ⟨Flow.code_8048, Flow.code_8049, Flow.code_8050, Flow.code_8051,
      Flow.code_8052, Flow.code_8053, Flow.code_8054, Flow.code_8055,
      trivial⟩
  · exact ⟨Flow.code_8074, Flow.code_8075, Flow.code_8076, Flow.code_8077,
      Flow.code_8078, Flow.code_8079, Flow.code_8080, Flow.code_8081,
      trivial⟩
  · exact ⟨Flow.code_8100, Flow.code_8101, Flow.code_8102, Flow.code_8103,
      Flow.code_8104, Flow.code_8105, Flow.code_8106, Flow.code_8107,
      trivial⟩
  · exact ⟨Flow.code_8126, Flow.code_8127, Flow.code_8128, Flow.code_8129,
      Flow.code_8130, Flow.code_8131, Flow.code_8132, Flow.code_8133,
      trivial⟩
  · exact ⟨Flow.code_8152, Flow.code_8153, Flow.code_8154, Flow.code_8155,
      Flow.code_8156, Flow.code_8157, Flow.code_8158, Flow.code_8159,
      trivial⟩
  · exact ⟨Flow.code_8178, Flow.code_8179, Flow.code_8180, Flow.code_8181,
      Flow.code_8182, Flow.code_8183, Flow.code_8184, Flow.code_8185,
      trivial⟩
  · exact ⟨Flow.code_8204, Flow.code_8205, Flow.code_8206, Flow.code_8207,
      Flow.code_8208, Flow.code_8209, Flow.code_8210, Flow.code_8211,
      trivial⟩
  · exact ⟨Flow.code_8241, Flow.code_8242, Flow.code_8243, Flow.code_8244,
      Flow.code_8245, Flow.code_8246, Flow.code_8247, Flow.code_8248,
      trivial⟩
  · exact ⟨Flow.code_8267, Flow.code_8268, Flow.code_8269, Flow.code_8270,
      Flow.code_8271, Flow.code_8272, Flow.code_8273, Flow.code_8274,
      trivial⟩
  · exact ⟨Flow.code_8293, Flow.code_8294, Flow.code_8295, Flow.code_8296,
      Flow.code_8297, Flow.code_8298, Flow.code_8299, Flow.code_8300,
      trivial⟩
  · exact ⟨Flow.code_8319, Flow.code_8320, Flow.code_8321, Flow.code_8322,
      Flow.code_8323, Flow.code_8324, Flow.code_8325, Flow.code_8326,
      trivial⟩
  · exact ⟨Flow.code_8345, Flow.code_8346, Flow.code_8347, Flow.code_8348,
      Flow.code_8349, Flow.code_8350, Flow.code_8351, Flow.code_8352,
      trivial⟩
  · exact ⟨Flow.code_8371, Flow.code_8372, Flow.code_8373, Flow.code_8374,
      Flow.code_8375, Flow.code_8376, Flow.code_8377, Flow.code_8378,
      trivial⟩
  · exact ⟨Flow.code_8397, Flow.code_8398, Flow.code_8399, Flow.code_8400,
      Flow.code_8401, Flow.code_8402, Flow.code_8403, Flow.code_8404,
      trivial⟩
  · exact ⟨Flow.code_8423, Flow.code_8424, Flow.code_8425, Flow.code_8426,
      Flow.code_8427, Flow.code_8428, Flow.code_8429, Flow.code_8430,
      trivial⟩

theorem rescaleUnpackCode (stage : Fin 2) (chunk : Fin 8) :
    UnpackCode kernel (rescaleLoadPc stage chunk + 1 + (rescalePacks stage chunk).length + 8)
      (rescaleUnpacks stage chunk) := by
  fin_cases stage <;> fin_cases chunk
  · exact ⟨Flow.code_8030, Flow.code_8031, Flow.code_8032, Flow.code_8033,
      Flow.code_8034, Flow.code_8035, Flow.code_8036, Flow.code_8037,
      trivial⟩
  · exact ⟨Flow.code_8056, Flow.code_8057, Flow.code_8058, Flow.code_8059,
      Flow.code_8060, Flow.code_8061, Flow.code_8062, Flow.code_8063,
      trivial⟩
  · exact ⟨Flow.code_8082, Flow.code_8083, Flow.code_8084, Flow.code_8085,
      Flow.code_8086, Flow.code_8087, Flow.code_8088, Flow.code_8089,
      trivial⟩
  · exact ⟨Flow.code_8108, Flow.code_8109, Flow.code_8110, Flow.code_8111,
      Flow.code_8112, Flow.code_8113, Flow.code_8114, Flow.code_8115,
      trivial⟩
  · exact ⟨Flow.code_8134, Flow.code_8135, Flow.code_8136, Flow.code_8137,
      Flow.code_8138, Flow.code_8139, Flow.code_8140, Flow.code_8141,
      trivial⟩
  · exact ⟨Flow.code_8160, Flow.code_8161, Flow.code_8162, Flow.code_8163,
      Flow.code_8164, Flow.code_8165, Flow.code_8166, Flow.code_8167,
      trivial⟩
  · exact ⟨Flow.code_8186, Flow.code_8187, Flow.code_8188, Flow.code_8189,
      Flow.code_8190, Flow.code_8191, Flow.code_8192, Flow.code_8193,
      trivial⟩
  · exact ⟨Flow.code_8212, Flow.code_8213, Flow.code_8214, Flow.code_8215,
      Flow.code_8216, Flow.code_8217, Flow.code_8218, Flow.code_8219,
      trivial⟩
  · exact ⟨Flow.code_8249, Flow.code_8250, Flow.code_8251, Flow.code_8252,
      Flow.code_8253, Flow.code_8254, Flow.code_8255, Flow.code_8256,
      trivial⟩
  · exact ⟨Flow.code_8275, Flow.code_8276, Flow.code_8277, Flow.code_8278,
      Flow.code_8279, Flow.code_8280, Flow.code_8281, Flow.code_8282,
      trivial⟩
  · exact ⟨Flow.code_8301, Flow.code_8302, Flow.code_8303, Flow.code_8304,
      Flow.code_8305, Flow.code_8306, Flow.code_8307, Flow.code_8308,
      trivial⟩
  · exact ⟨Flow.code_8327, Flow.code_8328, Flow.code_8329, Flow.code_8330,
      Flow.code_8331, Flow.code_8332, Flow.code_8333, Flow.code_8334,
      trivial⟩
  · exact ⟨Flow.code_8353, Flow.code_8354, Flow.code_8355, Flow.code_8356,
      Flow.code_8357, Flow.code_8358, Flow.code_8359, Flow.code_8360,
      trivial⟩
  · exact ⟨Flow.code_8379, Flow.code_8380, Flow.code_8381, Flow.code_8382,
      Flow.code_8383, Flow.code_8384, Flow.code_8385, Flow.code_8386,
      trivial⟩
  · exact ⟨Flow.code_8405, Flow.code_8406, Flow.code_8407, Flow.code_8408,
      Flow.code_8409, Flow.code_8410, Flow.code_8411, Flow.code_8412,
      trivial⟩
  · exact ⟨Flow.code_8431, Flow.code_8432, Flow.code_8433, Flow.code_8434,
      Flow.code_8435, Flow.code_8436, Flow.code_8437, Flow.code_8438,
      trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
