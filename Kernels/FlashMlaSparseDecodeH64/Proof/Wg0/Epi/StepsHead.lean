-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup
public import Lemmas.Flow.StoreU
public import Lemmas.Flow.BranchJoinU
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018

@[expose] public section

/-! # Warpgroup 0's obligations at the head of the epilogue (pcs 1154–1200)

The row-sum exchange (`ebar0`, `est`, `ebar1`, `eld`; the head test at pc 1161 on `%p118`), the
LSE store (`lse`), the poll of the O-ready barrier (`wsv`), and the fence (`efa`) whose segment
crosses the row-sum test at pc 1191 (a data predicate: both sides meet at pc 1197,
`SegU.branch_join`) to the first output load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

theorem stepAt_ebar0 (d : D) (hs : d.site = .ebar0) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_1154 by exact fires_barSyncN_next hf
  w0_seg

theorem stepAt_est (d : D) (hs : d.site = .est) : (code P L g w).StepAtU d := by
  w0_site
  refine Code.scalarStoreU Flow.code_1155 rfl rfl rfl (fun _ => rfl) rfl rfl rfl rfl Nat.one_pos ?_
  w0_seg

theorem stepAt_ebar1 (d : D) (hs : d.site = .ebar1) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_1156 by exact fires_barSyncN_next hf
  w0_seg

/-- **The LSE stretch** (pcs 1162–1177, under the head test): the LSE value (data), then the
three `ld.param`s of the LSE pointer and strides with the address chain between them. -/
theorem lseSeg (hp : Pre P L m) (s s' : Site) (a0 : Value) (l0 l1 cnt bi vs pv sl ps : BitVec 64)
    (vt : Bool) :
    SegU kernel Assumptions.all L g 1162
      (vF P L g w 1161 ⟨s, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) 1178
      (vF P L g w 1178 ⟨s', 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) := by
  w0_ldp 1167 Flow.code_1167 96 P.lseBase 8 ⟨s, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
  w0_ldp 1169 Flow.code_1169 180 (P.s_q * 64) 4 ⟨s, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
  w0_ldp 1171 Flow.code_1171 184 64 4 ⟨s, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
  w0_seg

set_option hygiene false in
/-- The row-sum read, then the head test to the site `S` (`h` fixes its side). -/
local macro "eld_at " S:term:max h:term:max : tactic => `(tactic| (
  refine Code.step_loadU (d' := ⟨$S, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) Flow.code_1157
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ _ => by simp only [code, succ, dataRd, afterEld, $h:term, ↓reduceIte] <;> rfl)
    Nat.one_pos (by
      change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys]
      show _ ∉ ctlLive 1157; decide +kernel) ?_
  w0_ldp 1159 Flow.code_1159 8 64 4 ⟨.eld, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
  w0_br 1161 Flow.code_1161 118 (scmp .ge .s (r5W L g) (pw 64)) $h
    ⟨.eld, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩))

/-- The row-sum read: the LSE store unless the head is beyond the heads. -/
theorem stepAt_eld (hp : Pre P L m) (d : D) (hs : d.site = .eld) :
    (code P L g w).StepAtU d := by
  w0_site
  cases h : scmp .ge .s (r5W L g) (pw 64)
  · eld_at .lse h
    exact lseSeg hp .eld .lse a0 l0 l1 cnt bi vs pv sl ps vt
  · eld_at .wsv h
    w0_seg

theorem stepAt_lse (d : D) (hs : d.site = .lse) : (code P L g w).StepAtU d := by
  w0_site
  refine Code.scalarStoreU Flow.code_1178 rfl rfl rfl (fun _ => rfl) rfl rfl rfl rfl Nat.one_pos ?_
  w0_seg

theorem stepAt_wsv (d : D) (hs : d.site = .wsv) : (code P L g w).StepAtU d := by
  w0_site
  w0_poll .efa via Flow.code_1184, Flow.code_1185, Flow.code_1186

/-- The fence, then over the row-sum test (both sides meet at pc 1197) and the descriptor
address `%rd843 = param_1 + 512` (pc 1197, the parameter-pointer reading) to the first output
load. -/
theorem stepAt_efa (hp : Pre P L m) (d : D) (hs : d.site = .efa) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_1187 by exact Code.fires_tcPlain_next (.inl rfl) hf
  refine SegU.comp (b := 1191) (G := vF P L g w 1191
    ⟨.efa, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) (by w0_seg) ?_
  have h1197 : SegU kernel Assumptions.all L g 1197
      (vF P L g w 1191 ⟨.efa, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) (Site.old 0).pc
      (facts P L g w ⟨.old 0, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) := by
    refine SegU.comp (SegU.of_seg (n := 1) (fun t ht => ⟨_, run_paramAdd (pc := 1197) (k := 512)
      Flow.code_1197 ht (by decide) (holds_mem (atHolds ht) (mem_factsFrom_eq
        (by decide +kernel) rfl)) hp.param1Object (by decide),
      At.set ht (fresh_live (by decide +kernel))⟩)) ?_
    w0_seg
  exact SegU.branch_join Flow.code_1191 bra_rule noSegments.segFreePc h1197
    (SegU.comp (b := 1197) (G := vF P L g w 1191
      ⟨.efa, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) (by w0_seg) h1197)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
