-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProATac

@[expose] public section

/-! # The prologue's local segments, pc 224 to 410

Each lemma is one run of local instructions between two checkpoints, from the registers live at
the first (valued by the table of the thread's data) to the registers live at the second. A run
that starts after an election carries the facts of the election's result (the predicate of the
elected lane and of the guard, `a` and `b`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

seg_elect seg_224_227_miss 224 227 59 61 miss [v_p56, v_r227]
seg_elect seg_229_231_hit 229 231 59 62 hit [v_p57, v_r229]
seg_elect seg_229_232_miss 229 232 59 62 miss [v_p57, v_r229]
seg_run seg_232_233 232 233 [v_p63]
seg_run seg_234_236 234 236 [v_r250, v_r251]
seg_run seg_237_238_skip 237 238 skip 177
seg_run seg_238_241 238 241 [v_r252, v_rd125, v_r240]
seg_run seg_242_243 242 243 [v_r243]
seg_elect seg_256_259_hit 256 259 59 69 hit [v_p65, v_r244, v_r245]
seg_elect seg_256_262_miss 256 262 59 69 miss [v_p65, v_r244, v_r245, v_rd126, v_r246]
seg_run seg_260_262 260 262 [v_rd126, v_r246]
seg_run seg_263_264 263 264 [v_r248]
seg_elect seg_266_268_hit 266 268 59 70 hit [v_p66, v_r247]
seg_elect seg_266_269_miss 266 269 59 70 miss [v_p66, v_r247]
seg_elect seg_271_273_hit 271 273 59 71 hit [v_p67, v_r249]
seg_elect seg_271_274_miss 271 274 59 71 miss [v_p67, v_r249]
seg_run seg_274_275 274 275 [v_p72]
seg_run seg_276_278 276 278 [v_r272, v_r273]
seg_run seg_279_280_skip 279 280 skip 177
seg_run seg_280_283 280 283 [v_r274, v_rd127, v_r262]
seg_run seg_284_285 284 285 [v_r265]
seg_elect seg_298_301_hit 298 301 59 78 hit [v_p74, v_r266, v_r267]
seg_elect seg_298_304_miss 298 304 59 78 miss [v_p74, v_r266, v_r267, v_rd128, v_r268]
seg_run seg_302_304 302 304 [v_rd128, v_r268]
seg_run seg_305_306 305 306 [v_r270]
seg_elect seg_308_310_hit 308 310 59 79 hit [v_p75, v_r269]
seg_elect seg_308_311_miss 308 311 59 79 miss [v_p75, v_r269]
seg_elect seg_313_315_hit 313 315 59 80 hit [v_p76, v_r271]
seg_elect seg_313_316_miss 313 316 59 80 miss [v_p76, v_r271]
seg_param seg_316_317 316 "25" x25
seg_param seg_317_318 317 "11" x11
seg_param seg_318_319 318 "10" x10

/-- **`add.s32 %r30, %r2, 256`** (pc 319) on the base word the common start loaded: `%r30` is
Core's outcome `r30Of`, or the instruction faults (`Raw.addImmE` is an error) and the thread is
dead. -/
theorem segD_319_320 (L : Launch) (g : Nat) (dt : Dat) :
    SegD kernel asms L g 1 319 (factsAt L g 319 dt) 320 (factsAt L g 320 dt)
      (∃ x, Raw.addImmE dt.w 256 = .ok x) := by
  have hreg : ∀ t : TState, At t 319 (factsAt L g 319 dt) → t.regs 463 = some dt.w := by
    intro t h
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (show 463 ∈ Flow.live 319 by decide +kernel))
    rwa [valueOf_463] at this
  intro t h
  refine ⟨fun ⟨x, hx⟩ => ?_, fun hn => ?_⟩
  · refine Raw.seg_int1 (d := 491) (v := x) Flow.code_319 rfl rfl
      (asms_segFree (by decide +kernel)) (fun t' h' => Raw.execInt_addImm_ok (hreg t' h') hx)
      (fun R hR => ?_) t h
    unfold factsAt at hR ⊢
    exact Raw.holds_set_live hR (by rw [valueOf_491]; simp [r30Of, hx]) (by decide +kernel)
  · exact Raw.dead_int1 Flow.code_319 rfl rfl (asms_segFree (by decide +kernel))
      (fun t' h' => Raw.execInt_addImm_err (hreg t' h') (fun x hx => hn ⟨x, hx⟩)) h

seg_run seg_320_331 320 331 [v_rd257, v_rd129, v_rd130, v_rd131, v_rd132, v_rd133, v_rd134, v_rd135,
    v_rd136, v_rd137]
seg_run seg_331_343 331 343 [v_rd138, v_rd139, v_rd140, v_rd141, v_rd142, v_rd143, v_rd144, v_rd145,
    v_rd146, v_rd147, v_rd148, v_rd149]
seg_run seg_343_355 343 355 [v_rd150, v_rd151, v_rd152, v_rd153, v_rd154, v_rd155, v_rd156, v_rd157,
    v_rd158, v_rd159, v_rd160, v_rd161]
seg_run seg_355_367 355 367 [v_rd162, v_rd163, v_rd164, v_rd165, v_rd166, v_rd167, v_rd168, v_rd169,
    v_rd170, v_rd171, v_rd172, v_rd173]
seg_run seg_367_379 367 379 [v_rd174, v_rd175, v_rd176, v_rd177, v_rd178, v_rd179, v_rd180, v_rd181,
    v_rd182, v_rd183, v_rd184, v_rd185]
seg_run seg_379_387 379 387 [v_rd186, v_rd187, v_rd188, v_rd189, v_rd190, v_rd191, v_rd192, v_rs18]
seg_run seg_387_388 387 388 q 0 1
seg_run seg_387_399_skipG 387 399 skip 81 q 0 6
seg_run seg_399_411_skipG 399 411 skip 81 q 6 12

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
