-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictF
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictSink
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.Stage
public import Lemmas.Flow.SegFrameSet
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part001
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part002

@[expose] public section

/-! # Warpgroup 0's strict window after the `setmaxnreg` (pcs 104 to the next site)

The staging stretch (`stageSegS`), the scale word and the sink's base pointer (`ld.param`, pcs 146
and 147), the two tests that skip the sink's load (pcs 148-153), and from pc 158 the sink-less
stretch (`sinkSegS`). The scale word and the sink word `-inf` are carried to the end. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- One local instruction that writes the register `d` of the table: the exact piece. -/
theorem segS_live {live : Nat → List Nat} {val : Nat → Value} {pc d : Nat} {op : Op}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true) (hd : d ∉ live pc)
    (hlive : ∀ x ∈ live (pc + 1), x ∈ d :: live pc)
    (hex : ∀ t, At t pc (factsFrom (live pc) val) →
      execLocalA Assumptions.all L g t op = .ok (PTX.next (setReg t d (val d)))) :
    ∃ n, Seg kernel Assumptions.all L g n pc (factsFrom (live pc) val) (pc + 1)
      (factsFrom (live (pc + 1)) val) := by
  refine ⟨1, fun t ht => ?_⟩
  refine ⟨_, run_local hc hl ht (hex t ht), ?_⟩
  have hs := At.set (v := val d) ht (not_mem_factsFrom hd)
  obtain ⟨-, -, -, -, hsR⟩ := id hs
  refine At.mono hs (holds_of_pointwise fun x hx => holds_mem hsR ?_)
  rcases List.mem_cons.mp (hlive x hx) with rfl | h
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (mem_factsFrom h)

set_option hygiene false in
/-- One pointer addition of the immediate `k` at `pc` (code lemma `c`) from register `r`. -/
macro "st_addS " c:term:max r:term:max k:term:max : tactic => `(tactic| (
  refine segS_live (live := ctlLive) (val := valueOf P L g w d) (d := $r) $c rfl
    (by decide +kernel) (by decide +kernel) fun t ht => ?_
  obtain ⟨hpc, -, -, -, hR⟩ := ht
  exact exec_add_sharedPtr (k := $k) (regs_of_factsFrom hR (by decide +kernel))
    (.inr rfl) (by omega) (by decide) (by decide)
    (fun a ha => asms_localRule_int (by rw [hpc]; decide) (by rw [hpc]; decide)
      (by rw [hpc]; decide) (Assumptions.peerPackRule_of_none (by rw [hpc]; rfl)) a ha)))

set_option hygiene false in
/-- Chunk `k`'s shift, mask and xor into the staging register `r`, exactly. -/
macro "st_swzS " h:term:max r:term:max k:term:max : tactic => `(tactic| (
  refine ⟨3, fun t ht => ?_⟩
  seg_fp ht using
    (try (rw [st_keep_ne rfl (by omega)]; simp only [Function.update_apply]
          split_ifs <;> first | rfl | (exfalso; omega)))
    (try (nf_simp
          rw [show valueOf P L g w d $r = shP L g (stW L g $k) from rfl, st_norm $h]
          dsimp only [shP, stW, stM]
          rw [stage_xor $h]))))

/-- **The staging stretch, exactly** (pcs 104-145): the `cvta.shared` needs the thread to be
launched. -/
theorem stageSegS (hp : Pre P L m) (hg : g < L.threads ∧ g / L.block < L.grid) (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 104 (vF P L g w 103 d) 146 (vF P L g w 146 d) := by
  have hs := sharedBase_lt hp
  have hq := stQuad_lt L g
  refine Seg.comp_ex (q := 110) (H := vF P L g w 110 d) (by seg_sym using w0_segS) ?_
  refine Seg.comp_ex (q := 111) (H := vF P L g w 111 d) ?_ ?_
  · refine segS_live (live := ctlLive) (val := valueOf P L g w d) (d := 3111) Flow.code_110 rfl
      (by decide +kernel) (by decide +kernel) fun t ht => ?_
    obtain ⟨hpc, -, -, -, hR⟩ := ht
    have hr := regs_of_factsFrom hR (r := 3110) (by decide +kernel)
    change t.regs 3110 = some (.bits 64 (zext (sbw L))) at hr
    rw [zext_sbw hp] at hr
    exact exec_cvtaShared (cl := false) (toShared := false)
      (readSharedAddress_bits hr (.inr rfl) hg.1 hg.2 (by omega)) rfl
      (localRule_none_addr t _) noSegments.segFreePc
  refine Seg.comp_ex (q := 113) (H := vF P L g w 113 d) (by seg_sym using w0_segS) ?_
  refine Seg.comp_ex (q := 114) (H := vF P L g w 114 d) ?_ ?_
  · refine segS_live (live := ctlLive) (val := valueOf P L g w d) (d := 3113) Flow.code_113 rfl
      (by decide +kernel) (by decide +kernel) fun t ht => ?_
    obtain ⟨hpc, -, -, -, hR⟩ := ht
    have hq' := regs_of_factsFrom hR (r := 3112) (by decide +kernel)
    change t.regs 3112 = some (.bits 64 (stQuad L g)) at hq'
    have hq'' : t.regs 3112 = some (.bits 64 (BitVec.ofNat 64 (stQuad L g).toNat)) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hq'
    exact exec_add_sharedPtr_reg (regs_of_factsFrom hR (r := 3111) (by decide +kernel))
      hq'' (.inr rfl) (by omega) (by omega) rfl (by decide)
      (fun a ha => asms_localRule_int (by rw [hpc]; decide) (by rw [hpc]; decide)
        (by rw [hpc]; decide) (Assumptions.peerPackRule_of_none (by rw [hpc]; rfl)) a ha)
      noSegments.segFreePc
  refine Seg.comp_ex (q := 115) (H := vF P L g w 115 d) (by st_addS Flow.code_114 3114 65536) ?_
  refine Seg.comp_ex (q := 118) (H := vF P L g w 118 d)
    (by st_swzS (stP_lt hp g (k := 0) (by decide)) 2992 0) ?_
  refine Seg.comp_ex (q := 119) (H := vF P L g w 119 d)
    (by st_addS Flow.code_118 3117 65552) ?_
  refine Seg.comp_ex (q := 122) (H := vF P L g w 122 d)
    (by st_swzS (stP_lt hp g (k := 1) (by decide)) 2993 1) ?_
  refine Seg.comp_ex (q := 123) (H := vF P L g w 123 d)
    (by st_addS Flow.code_122 3120 65568) ?_
  refine Seg.comp_ex (q := 126) (H := vF P L g w 126 d)
    (by st_swzS (stP_lt hp g (k := 2) (by decide)) 2994 2) ?_
  refine Seg.comp_ex (q := 127) (H := vF P L g w 127 d)
    (by st_addS Flow.code_126 3123 65584) ?_
  refine Seg.comp_ex (q := 130) (H := vF P L g w 130 d)
    (by st_swzS (stP_lt hp g (k := 3) (by decide)) 2995 3) ?_
  refine Seg.comp_ex (q := 131) (H := vF P L g w 131 d)
    (by st_addS Flow.code_130 3126 65600) ?_
  refine Seg.comp_ex (q := 134) (H := vF P L g w 134 d)
    (by st_swzS (stP_lt hp g (k := 4) (by decide)) 2996 4) ?_
  refine Seg.comp_ex (q := 135) (H := vF P L g w 135 d)
    (by st_addS Flow.code_134 3129 65616) ?_
  refine Seg.comp_ex (q := 138) (H := vF P L g w 138 d)
    (by st_swzS (stP_lt hp g (k := 5) (by decide)) 2997 5) ?_
  refine Seg.comp_ex (q := 139) (H := vF P L g w 139 d)
    (by st_addS Flow.code_138 3132 65632) ?_
  refine Seg.comp_ex (q := 142) (H := vF P L g w 142 d)
    (by st_swzS (stP_lt hp g (k := 6) (by decide)) 2998 6) ?_
  refine Seg.comp_ex (q := 143) (H := vF P L g w 143 d)
    (by st_addS Flow.code_142 3135 65648) ?_
  st_swzS (stP_lt hp g (k := 7) (by decide)) 2999 7

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

set_option hygiene false in
local macro "ldp_at " c:term:max ty:term:max off:term:max d:term:max n:term:max x:term:max :
    tactic => `(tactic| (
  refine ldp_ex (ty := $ty) (off := $off) (d := $d) (n := $n) (x := $x) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields])
    (by repeat (first | exact mem_factsFrom_eq (by decide +kernel) rfl |
      apply List.mem_cons_of_mem))
    (by simp only [List.map_cons, factsFrom_keys]; decide +kernel) ?_))

/-- The positions of the stretches after the sink's tests (the staging's data frame). -/
def smrS : List Nat :=
  [147, 148, 149, 150, 151, 152, 153, 154, 155, 158, 159, 160,
   161, 162, 163, 164, 165, 166, 167, 170, 171, 172, 173, 174,
   175, 176, 177, 178, 179, 180, 183, 184, 185, 186, 187, 188,
   189, 190, 191, 192, 193, 194, 195, 196, 197, 1836, 1837, 1838, 1839]

/-- The scale word and the sink word `-inf`. -/
def smrData (L : Launch) : List (Nat × Value) :=
  [(467, .bits 32 (BitVec.ofNat 64 (leNat (scaleBits L) 0 4))),
   (2880, w32 (BitVec.ofNat 64 4286578688))]

/-- From pc 158 on, with the scale word and the sink word carried. -/
theorem smrArm (hp : Pre P L m) (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 158 (smrData L ++ factsFrom (ctlLive 158)
      (valueOf P L g w d)) ((code P L g w).pc (afterSink P L g w d))
      ((code P L g w).facts (afterSink P L g w d) ++ smrData L) := by
  obtain ⟨n, h⟩ := sinkSegS (w := w) hp d
  have h' := Seg.frameSet (H := smrData L) rulesFrame (S := smrS)
    (by simp only [smrData, List.map_cons, List.map_nil]; kernel_rfl)
    (fun _ _ => PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree _) (by kernel_rfl) h
  exact ⟨n, h'.weaken_start fun R hR => by
    obtain ⟨hd, hc⟩ := (holds_append _ _ _).mp hR
    exact (holds_append _ _ _).mpr ⟨hc, hd⟩⟩

theorem smr_v2880 (d : D) :
    valueOf P L g w d 2880 = w32 (BitVec.ofNat 64 4286578688) := rfl

/-- The facts at a later position, from those at the checkpoint of the tests. -/
theorem smrStart {R : Nat → Option Value} {pc : Nat} {d : D}
    (h : Holds R ((467, .bits 32 (BitVec.ofNat 64 (leNat (scaleBits L) 0 4))) ::
      factsFrom (ctlLive pc) (valueOf P L g w d))) (h2880 : 2880 ∈ ctlLive pc)
    {pc' : Nat} (hs : ∀ r ∈ ctlLive pc', r ∈ ctlLive pc) :
    Holds R (smrData L ++ factsFrom (ctlLive pc') (valueOf P L g w d)) := by
  obtain ⟨h1, hc⟩ := h
  refine (holds_append _ _ _).mpr ⟨⟨h1, ?_, trivial⟩, holds_factsFrom_mono hc hs⟩
  rw [← smr_v2880 (P := P) (L := L) (g := g) (w := w) d]
  exact holds_mem hc (mem_factsFrom h2880)

/-- The tests after the sink's pointer (pcs 150-153) and the sink's load site or the stretch
after it. -/
theorem smrTest2 (hp : Pre P L m) (d : D)
    (h69 : eqz64 (pw8 (P.sinkBase.getD 0)) = false) :
    ∃ n, Seg kernel Assumptions.all L g n 150
      ((467, .bits 32 (BitVec.ofNat 64 (leNat (scaleBits L) 0 4))) ::
        factsFrom (ctlLive 150) (valueOf P L g w d))
      ((code P L g w).pc (afterSmr P L g w d))
      ((code P L g w).facts (afterSmr P L g w d) ++ smrData L) := by
  refine Seg.comp_ex (q := 151) (H := (467, .bits 32 (BitVec.ofNat 64 (leNat (scaleBits L) 0 4)))
    :: factsFrom (ctlLive 151) (valueOf P L g w d)) (by seg_sym using w0_segS) ?_
  ldp_at Flow.code_151 (.int .b 32) 8 931 4 64
  refine Seg.comp_ex (q := 153) (H := (467, .bits 32 (BitVec.ofNat 64 (leNat (scaleBits L) 0 4)))
    :: factsFrom (ctlLive 153) (valueOf P L g w d)) (by seg_sym using w0_segS) ?_
  cases h70 : scmp .ge .s (r10W L g) (pw 64)
  · rw [show afterSmr P L g w d = { d with site := .sink } by
      simp only [afterSmr, h69, h70, Bool.or_self, Bool.false_eq_true, ↓reduceIte]]
    refine Seg.pred_ex (p := 70) (c := scmp .ge .s (r10W L g) (pw 64)) (c' := false)
      (List.mem_cons_of_mem _ (mem_factsFrom_eq (by decide +kernel) rfl)) h70 ?_
    refine Seg.comp_ex (q := 154) ⟨1, Seg.bra (target := 158) (p := 70) (pick := false)
      Flow.code_153 (List.mem_cons_self ..) (fun t _ a ha => bra_rule t a ha)
      (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 153)⟩ ?_
    refine Seg.weaken_end_ex (G := (467, .bits 32 (BitVec.ofNat 64 (leNat (scaleBits L) 0 4))) ::
      (2880, valueOf P L g w d 2880) :: factsFrom (ctlLive 156) (valueOf P L g w d))
      (by seg_sym using w0_segS) fun R hR => ?_
    obtain ⟨h1, h2, hc⟩ := hR
    refine (holds_append _ _ _).mpr ⟨hc, ⟨h1, ?_, trivial⟩⟩
    rw [← smr_v2880 (P := P) (L := L) (g := g) (w := w) d]
    exact h2
  · rw [show afterSmr P L g w d = afterSink P L g w d by
      simp only [afterSmr, h70, Bool.or_true, ↓reduceIte]]
    refine Seg.pred_ex (p := 70) (c := scmp .ge .s (r10W L g) (pw 64)) (c' := true)
      (List.mem_cons_of_mem _ (mem_factsFrom_eq (by decide +kernel) rfl)) h70 ?_
    refine Seg.comp_ex (q := 158) ⟨1, Seg.bra (target := 158) (p := 70) (pick := true)
      Flow.code_153 (List.mem_cons_self ..) (fun t _ a ha => bra_rule t a ha)
      (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 153)⟩ ?_
    obtain ⟨n, h⟩ := smrArm (w := w) hp d
    exact ⟨n, h.weaken_start fun R hR => by
      obtain ⟨-, hR⟩ := hR
      exact smrStart hR (by decide +kernel) (by decide +kernel)⟩

/-- **The window after the `setmaxnreg`** (pcs 104 to the next site), on the control table. -/
theorem smrSegS (hp : Pre P L m) (hg : g < L.threads ∧ g / L.block < L.grid) (d : D) :
    ∃ n, Seg kernel Assumptions.all L g n 104 (vF P L g w 103 d)
      ((code P L g w).pc (afterSmr P L g w d))
      ((code P L g w).facts (afterSmr P L g w d) ++ smrData L) := by
  obtain ⟨n0, h0⟩ := stageSegS (w := w) hp hg d
  refine Seg.comp_ex ⟨n0, h0⟩ ?_
  ldp_at Flow.code_146 (.int .b 32) 28 467 4 (scaleBits L)
  ldp_at Flow.code_147 (.int .b 64) 88 3000 8 (P.sinkBase.getD 0)
  refine Seg.comp_ex (q := 149) (H := (467, .bits 32 (BitVec.ofNat 64 (leNat (scaleBits L) 0 4)))
    :: factsFrom (ctlLive 149) (valueOf P L g w d)) (by seg_sym using w0_segS) ?_
  cases h69 : eqz64 (pw8 (P.sinkBase.getD 0))
  · refine Seg.pred_ex (p := 69) (c := eqz64 (pw8 (P.sinkBase.getD 0))) (c' := false)
      (List.mem_cons_of_mem _ (mem_factsFrom_eq (by decide +kernel) rfl)) h69 ?_
    refine Seg.comp_ex (q := 150) ⟨1, Seg.bra (target := 158) (p := 69) (pick := false)
      Flow.code_149 (List.mem_cons_self ..) (fun t _ a ha => bra_rule t a ha)
      (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 149)⟩ ?_
    obtain ⟨n, h⟩ := smrTest2 (w := w) hp d h69
    exact ⟨n, h.weaken_start fun R hR => by
      obtain ⟨-, h1, hc⟩ := hR
      exact ⟨h1, holds_factsFrom_mono hc (by decide +kernel)⟩⟩
  · refine Seg.pred_ex (p := 69) (c := eqz64 (pw8 (P.sinkBase.getD 0))) (c' := true)
      (List.mem_cons_of_mem _ (mem_factsFrom_eq (by decide +kernel) rfl)) h69 ?_
    refine Seg.comp_ex (q := 158) ⟨1, Seg.bra (target := 158) (p := 69) (pick := true)
      Flow.code_149 (List.mem_cons_self ..) (fun t _ a ha => bra_rule t a ha)
      (PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.w0SegFree 149)⟩ ?_
    rw [show afterSmr P L g w d = afterSink P L g w d by
      simp only [afterSmr, h69, Bool.true_or, ↓reduceIte]]
    obtain ⟨n, h⟩ := smrArm (w := w) hp d
    exact ⟨n, h.weaken_start fun R hR => by
      obtain ⟨-, hR⟩ := hR
      exact smrStart hR (by decide +kernel) (by decide +kernel)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
