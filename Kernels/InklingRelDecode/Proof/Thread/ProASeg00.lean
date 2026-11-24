-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProATac

@[expose] public section

/-! # The prologue's local segments, pc 20 to 226

Each lemma is one run of local instructions between two checkpoints, from the registers live at
the first (valued by the table of the thread's data) to the registers live at the second. A run
that starts after an election carries the facts of the election's result (the predicate of the
elected lane and of the guard, `a` and `b`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

seg_param seg_20_21 20 "17" x17
seg_param seg_21_22 21 "16" x16
seg_param seg_22_23 22 "15" x15
seg_param seg_23_24 23 "9" x9
seg_param seg_24_25 24 "8" x8
seg_param seg_25_26 25 "6" x6
seg_param seg_26_27 26 "0" x0
seg_run seg_28_34 28 34 [v_r17, v_r18, v_r19, v_rd110, v_rd107, v_r149]
seg_run seg_35_37 35 37 [v_rd108, v_r150]
seg_run seg_38_41 38 41 [v_r20, v_rd109, v_r151]
seg_run seg_42_54 42 54 [v_r21, v_r164, v_r165, v_r22, v_r166, v_r167, v_r168, v_r23, v_r169,
    v_r170, v_r171, v_r172]
seg_run seg_54_59 54 59 [v_r173, v_r24, v_r174, v_r175, v_r176]
seg_run seg_60_72 60 72 [v_r26, v_r27, v_r177, v_r178, v_r179, v_r28, v_rs1, v_rs2, v_rs3, v_p38,
    v_rs4, v_rs5]
seg_run seg_72_84 72 84 [v_r180, v_rs6, v_r181, v_rs7, v_r182, v_rs8, v_r183, v_p81, v_p82, v_p83,
    v_p39, v_p84]
seg_run seg_84_96 84 96 [v_r184, v_r185, v_r186, v_r187, v_rd111, v_rd112, v_rd113, v_rd114,
    v_rd115, v_rd116, v_rd117, v_rd118]
seg_run seg_96_108 96 108 [v_rd119, v_rd120, v_rd121, v_rd122, v_r29, v_rs9, v_rs10, v_rs11, v_rs12,
    v_rs13, v_rs14, v_rs15]
seg_run seg_108_120 108 120 [v_rs16, v_r188, v_r189, v_r190, v_r191, v_r192, v_r193, v_r194, v_r195,
    v_r196, v_r197, v_r198]
seg_run seg_120_130 120 130 [v_r199, v_r200, v_r201, v_r202, v_r203, v_rd3, v_rd4, v_rd5, v_rd6,
    v_p40]
seg_elect seg_131_134_hit 131 134 40 41 hit [v_p26, v_r205, v_r152]
seg_elect seg_131_135_miss 131 135 40 41 miss [v_p26, v_r205, v_r152]
seg_elect seg_136_138_hit 136 138 40 42 hit [v_p27, v_r153]
seg_elect seg_136_139_miss 136 139 40 42 miss [v_p27, v_r153]
seg_elect seg_140_142_hit 140 142 40 43 hit [v_p28, v_r154]
seg_elect seg_140_143_miss 140 143 40 43 miss [v_p28, v_r154]
seg_elect seg_144_146_hit 144 146 40 44 hit [v_p29, v_r155]
seg_elect seg_144_147_miss 144 147 40 44 miss [v_p29, v_r155]
seg_elect seg_148_150_hit 148 150 40 45 hit [v_p30, v_r156]
seg_elect seg_148_151_miss 148 151 40 45 miss [v_p30, v_r156]
seg_elect seg_152_154_hit 152 154 40 46 hit [v_p31, v_r157]
seg_elect seg_152_155_miss 152 155 40 46 miss [v_p31, v_r157]
seg_elect seg_156_158_hit 156 158 40 47 hit [v_p32, v_r158]
seg_elect seg_156_159_miss 156 159 40 47 miss [v_p32, v_r158]
seg_elect seg_160_162_hit 160 162 40 48 hit [v_p33, v_r159]
seg_elect seg_160_163_miss 160 163 40 48 miss [v_p33, v_r159]
seg_elect seg_164_166_hit 164 166 40 49 hit [v_p34, v_r160]
seg_elect seg_164_167_miss 164 167 40 49 miss [v_p34, v_r160]
seg_elect seg_168_170_hit 168 170 40 50 hit [v_p35, v_r161]
seg_elect seg_168_171_miss 168 171 40 50 miss [v_p35, v_r161]
seg_elect seg_172_174_hit 172 174 40 51 hit [v_p36, v_r162]
seg_elect seg_172_175_miss 172 175 40 51 miss [v_p36, v_r162]
seg_elect seg_176_178_hit 176 178 40 52 hit [v_p37, v_r163]
seg_elect seg_176_179_miss 176 179 40 52 miss [v_p37, v_r163]
seg_run seg_181_182 181 182 [v_r217]
seg_run seg_183_189 183 189 [v_r219, v_r31, v_r32, v_p53, v_r1451, v_p177]
seg_run seg_190_192 190 192 [v_r230, v_rd7]
seg_run seg_193_194_skip 193 194 skip 177
seg_run seg_194_197 194 197 [v_r231, v_rd123, v_r220]
seg_run seg_198_201 198 201 [v_r33, v_r223, v_r34]
seg_run seg_204_205 204 205 [v_p59]
seg_elect seg_214_217_hit 214 217 59 60 hit [v_p55, v_r224, v_r225]
seg_elect seg_214_220_miss 214 220 59 60 miss [v_p55, v_r224, v_r225, v_rd124, v_r226]
seg_run seg_218_220 218 220 [v_rd124, v_r226]
seg_run seg_221_222 221 222 [v_r228]
seg_elect seg_224_226_hit 224 226 59 61 hit [v_p56, v_r227]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
