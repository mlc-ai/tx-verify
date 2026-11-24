-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.StepLdw
public import Kernels.RmsNorm.Proof.Thread.Pieces

@[expose] public section

/-! # The output computation of a tile

After the last element of a tile's second reload: the weights convert to single precision
(`segAW`), each reloaded pair is packed and multiplied by the pair of scale factors (`segAP`), the
products by the pairs of weights (`segAQ`), and the results are converted to pairs of halves for
the output store (`segAC`), each instruction a piece (`pc_unpack32`, `pc_widen`, `pc_pack`,
`pc_mul`, `pc_unpack64`, `pc_mov`, `pc_cvt`). The machine continues when none of their outcomes
faults (`tileOk`); otherwise the thread is dead at the first that faults. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem segAW (d1 : D) :
    SegD kernel Prod L g 12 161 (factsAt P g 161 d1) 173 (factsAt P g 173 d1)
      (tileW d1.raw = true) := by
  have p161 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_161
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := p161
  have p162 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_162
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p162
  have p163 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_163
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p163
  have p164 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_164
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := S.comp p164
  have p165 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_165
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p165
  have p166 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_166
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p166
  have p167 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_167
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := S.comp p167
  have p168 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_168
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p168
  have p169 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_169
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p169
  have p170 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_170
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := S.comp p170
  have p171 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_171
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p171
  have p172 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_172
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p172
  exact S.iff (by simp only [tileW, Bool.and_eq_true]; exact Iff.rfl)

theorem segAP (d1 : D) :
    SegD kernel Prod L g 20 173 (factsAt P g 173 d1) 193 (factsAt P g 193 d1)
      (tileP d1.rs0 d1.rs1 (cpair d1.tt) = true) := by
  have p173 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_173
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := p173
  have p174 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_174
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p174
  have p175 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_175
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p175
  have p176 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_176
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p176
  have p177 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_177
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p177
  have p178 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_178
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p178
  have p179 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_179
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p179
  have p180 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_180
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p180
  have p181 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_181
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p181
  have p182 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_182
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p182
  have p183 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_183
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p183
  have p184 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_184
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p184
  have p185 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_185
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p185
  have p186 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_186
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p186
  have p187 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_187
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p187
  have p188 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_188
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p188
  have p189 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_189
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p189
  have p190 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_190
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p190
  have p191 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_191
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p191
  have p192 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_192
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p192
  exact S.iff (by simp only [tileP, Bool.and_eq_true]; exact Iff.rfl)

theorem segAQ (d1 : D) :
    SegD kernel Prod L g 24 193 (factsAt P g 193 d1) 217 (factsAt P g 217 d1)
      (tileQ d1.raw d1.rs0 d1.rs1 (cpair d1.tt) = true) := by
  have p193 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_193
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := p193
  have p194 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_194
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp p194
  have p195 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_195
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := SegD.seg_comp S p195
  have p196 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_196
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p196
  have p197 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_197
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p197
  have p198 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_198
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p198
  have p199 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_199
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p199
  have p200 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_200
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p200
  have p201 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_201
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p201
  have p202 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_202
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p202
  have p203 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_203
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p203
  have p204 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_204
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p204
  have p205 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_205
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p205
  have p206 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_206
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p206
  have p207 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_207
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p207
  have p208 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_208
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p208
  have p209 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_209
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p209
  have p210 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_210
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p210
  have p211 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_211
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p211
  have p212 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_212
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p212
  have p213 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_213
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p213
  have p214 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_214
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p214
  have p215 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_215
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p215
  have p216 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_216
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p216
  exact S.iff (by simp only [tileQ, Bool.and_eq_true]; exact Iff.rfl)

theorem segAC (d1 : D) :
    SegD kernel Prod L g 4 217 (factsAt P g 217 d1) 221 (factsAt P g 221 d1)
      (tileC d1.raw d1.rs0 d1.rs1 (cpair d1.tt) = true) := by
  have p217 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_217
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := p217
  have p218 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_218
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p218
  have p219 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_219
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p219
  have p220 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_220
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p220
  exact S.iff (by simp only [tileC, Bool.and_eq_true]; exact Iff.rfl)

theorem step_ldsa1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldsa1) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldsa1.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rms_hyps hpre
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs =>
      if tileOk d.raw d.rs0 vs (cpair d.tt) then some (tileA d vs) else none) := fun e => by
    simp only [next, hs]
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  have hpc : t.pc = Site.ldsa1.pc := h.1.trans (show d.site.pc = Site.ldsa1.pc by rw [hs])
  set d1 := tileA d ([a0, a1, a2] ++ [v]) with hd1
  have hU : At (afterVec t [162, 163, 164, 165] ([a0, a1, a2] ++ [v])) 161
      (factsAt P g 161 d1) := by
    refine ⟨by simp [afterVec, hpc]; rfl, rfl, rfl,
      by simp [afterVec, setRegs_fault, h.2.2.2.1], ?_⟩
    have hframe : ∀ r, r ∉ [162, 163, 164, 165] →
        (setRegs t [162, 163, 164, 165] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [162, 163, 164, 165] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  have hraw := hi.raw.2 (.inl hs)
  have S : SegD kernel Prod L g 60 161 (factsAt P g 161 d1) 221
      (factsAt P g 221 d1) (tileOk d.raw d.rs0 ([a0, a1, a2] ++ [v]) (cpair d.tt) = true) :=
    ((((segAW d1).comp (segAP d1)).comp (segAQ d1)).comp (segAC d1)).iff
      (by simp only [tileOk, Bool.and_eq_true]; exact Iff.rfl)
  have hS := S _ hU
  by_cases hok : tileOk d.raw d.rs0 ([a0, a1, a2] ++ [v]) (cpair d.tt) = true
  · obtain ⟨t2, hr2, ht2⟩ := hS.1 hok
    obtain ⟨t3, hr3, ht3⟩ : ∃ t', run kernel Prod L g 1 t2 = some t' ∧
        At t' Site.stoa.pc (facts P g d1) := by
      seg_fp ht2 using
        rms_values
        all_goals seg_close
    refine .inl ⟨d1, t3, by rw [hnext]; simp only [hok, ↓reduceIte, Option.map_some],
      (run_rtg hr2).trans (run_rtg hr3), atD_of rfl rfl ht3, ?_⟩
    have := hrow
    have := hraw
    simp only [hd1, tileA]
    inv_tac
  · exact .inr ⟨by rw [hnext]; simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.map_none],
      hS.2 hok⟩

theorem segBW (d1 : D) :
    SegD kernel Prod L g 12 226 (factsAt P g 226 d1) 238 (factsAt P g 238 d1)
      (tileW d1.raw = true) := by
  have p226 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_226
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := p226
  have p227 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_227
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p227
  have p228 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_228
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p228
  have p229 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_229
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := S.comp p229
  have p230 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_230
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p230
  have p231 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_231
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p231
  have p232 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_232
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := S.comp p232
  have p233 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_233
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p233
  have p234 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_234
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p234
  have p235 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_235
      (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
  have S := S.comp p235
  have p236 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_236
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p236
  have p237 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_237
      (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p237
  exact S.iff (by simp only [tileW, Bool.and_eq_true]; exact Iff.rfl)

theorem segBP (d1 : D) :
    SegD kernel Prod L g 20 238 (factsAt P g 238 d1) 258 (factsAt P g 258 d1)
      (tileP d1.rs0 d1.rs1 (cpair d1.tt) = true) := by
  have p238 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_238
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := p238
  have p239 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_239
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p239
  have p240 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_240
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p240
  have p241 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_241
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p241
  have p242 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_242
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p242
  have p243 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_243
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p243
  have p244 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_244
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p244
  have p245 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_245
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p245
  have p246 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_246
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p246
  have p247 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_247
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p247
  have p248 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_248
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p248
  have p249 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_249
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p249
  have p250 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_250
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p250
  have p251 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_251
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p251
  have p252 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_252
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p252
  have p253 := pc_pack (P := P) (L := L) (g := g) (d := d1) Flow.code_253
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p253
  have p254 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_254
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p254
  have p255 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_255
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p255
  have p256 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_256
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p256
  have p257 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_257
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p257
  exact S.iff (by simp only [tileP, Bool.and_eq_true]; exact Iff.rfl)

theorem segBQ (d1 : D) :
    SegD kernel Prod L g 24 258 (factsAt P g 258 d1) 282 (factsAt P g 282 d1)
      (tileQ d1.raw d1.rs0 d1.rs1 (cpair d1.tt) = true) := by
  have p258 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_258
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := p258
  have p259 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_259
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp p259
  have p260 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_260
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := SegD.seg_comp S p260
  have p261 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_261
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p261
  have p262 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_262
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p262
  have p263 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_263
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p263
  have p264 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_264
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p264
  have p265 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_265
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p265
  have p266 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_266
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p266
  have p267 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_267
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p267
  have p268 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_268
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p268
  have p269 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_269
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p269
  have p270 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_270
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p270
  have p271 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_271
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p271
  have p272 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_272
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p272
  have p273 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_273
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p273
  have p274 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_274
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p274
  have p275 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_275
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p275
  have p276 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_276
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p276
  have p277 := pc_packOk (P := P) (L := L) (g := g) (d := d1) Flow.code_277
      (by table_decide) (by table_decide) (by val_bytes) (by val_bytes) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p277
  have p278 := pc_mul (P := P) (L := L) (g := g) (d := d1) Flow.code_278
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p278
  have p279 := pc_unpack64 (P := P) (L := L) (g := g) (d := d1) Flow.code_279
      (by table_decide) (by decide) (unpackE_mulV _ _) (fun _ => rfl) (fun _ => rfl)
      (by table_decide)
  have S := S.comp_seg p279
  have p280 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_280
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p280
  have p281 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_281
      (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
  have S := S.comp_seg p281
  exact S.iff (by simp only [tileQ, Bool.and_eq_true]; exact Iff.rfl)

theorem segBC (d1 : D) :
    SegD kernel Prod L g 4 282 (factsAt P g 282 d1) 286 (factsAt P g 286 d1)
      (tileC d1.raw d1.rs0 d1.rs1 (cpair d1.tt) = true) := by
  have p282 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_282
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := p282
  have p283 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_283
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p283
  have p284 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_284
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p284
  have p285 := pc_cvt (P := P) (L := L) (g := g) (d := d1) Flow.code_285
      (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
  have S := S.comp p285
  exact S.iff (by simp only [tileC, Bool.and_eq_true]; exact Iff.rfl)

theorem step_ldsb1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldsb1) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldsb1.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rms_hyps hpre
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs =>
      if tileOk d.raw d.rs0 vs (cpair d.tt) then some (tileB d vs) else none) := fun e => by
    simp only [next, hs]
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  have hpc : t.pc = Site.ldsb1.pc := h.1.trans (show d.site.pc = Site.ldsb1.pc by rw [hs])
  set d1 := tileB d ([a0, a1, a2] ++ [v]) with hd1
  have hU : At (afterVec t [220, 221, 222, 223] ([a0, a1, a2] ++ [v])) 226
      (factsAt P g 226 d1) := by
    refine ⟨by simp [afterVec, hpc]; rfl, rfl, rfl,
      by simp [afterVec, setRegs_fault, h.2.2.2.1], ?_⟩
    have hframe : ∀ r, r ∉ [220, 221, 222, 223] →
        (setRegs t [220, 221, 222, 223] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [220, 221, 222, 223] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  have hraw := hi.raw.2 (.inr hs)
  have S : SegD kernel Prod L g 60 226 (factsAt P g 226 d1) 286
      (factsAt P g 286 d1) (tileOk d.raw d.rs0 ([a0, a1, a2] ++ [v]) (cpair d.tt) = true) :=
    ((((segBW d1).comp (segBP d1)).comp (segBQ d1)).comp (segBC d1)).iff
      (by simp only [tileOk, Bool.and_eq_true]; exact Iff.rfl)
  have hS := S _ hU
  by_cases hok : tileOk d.raw d.rs0 ([a0, a1, a2] ++ [v]) (cpair d.tt) = true
  · obtain ⟨t2, hr2, ht2⟩ := hS.1 hok
    obtain ⟨t3, hr3, ht3⟩ : ∃ t', run kernel Prod L g 1 t2 = some t' ∧
        At t' Site.stob.pc (facts P g d1) := by
      seg_fp ht2 using
        rms_values
        all_goals seg_close
    refine .inl ⟨d1, t3, by rw [hnext]; simp only [hok, ↓reduceIte, Option.map_some],
      (run_rtg hr2).trans (run_rtg hr3), atD_of rfl rfl ht3, ?_⟩
    have := hrow
    have := hraw
    simp only [hd1, tileB]
    inv_tac
  · exact .inr ⟨by rw [hnext]; simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.map_none],
      hS.2 hok⟩

end
end PTX.Kernels.RmsNorm.Proof
