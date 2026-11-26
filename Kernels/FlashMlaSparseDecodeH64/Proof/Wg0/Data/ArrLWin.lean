-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictF
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataFacts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.DeadPack
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup
public import Lemmas.Flow.Selp
public import Lemmas.Flow.SegFrameSet
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part002
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part003

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- The scale pair's pack at pc 208. -/
def pack208 : Op :=
  .move ⟨.pack, .int .b 64, [some 3144], [.reg 467, .reg 950]⟩

/-- At pc 208 every assumption other than `sharedBits` declines the pack. -/
theorem execLocalA_208 {t : TState} (hpc : t.pc = 208) :
    execLocalA Assumptions.all L g t pack208 =
      (Assumptions.deadPackRule L g t pack208).getD (execLocal L g t pack208) := by
  have hpa : t.pc ∉ paramAdds := by simp [paramAdds, hpc]
  have hpf : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites, hpc]
  have hsb : Assumptions.sharedBitsSites.contains t.pc = false := by
    simp [Assumptions.sharedBitsSites, hpc]
  rw [execLocalA_noSegment (fun a ha => noSegments a ha L g t), execLocalRule]
  simp only [Assumptions.all, List.findSome?_cons, List.findSome?_nil]
  have hpar : Assumptions.paramPointers.localRule L g t pack208 = none := by
    simp [Assumptions.paramPointers, hpa, hpf]
  have hsh : Assumptions.sharedBits.localRule L g t pack208 =
      Assumptions.deadPackRule L g t pack208 := by
    simp only [Assumptions.sharedBits, hsb, Bool.false_eq_true, ↓reduceIte]
    unfold Assumptions.deadPackRule pack208
    rw [hpc]
    simp [Assumptions.deadPackWords, Option.orElse, Assumptions.peerPackRule]
  rw [show Assumptions.idealArith.localRule L g t pack208 = none from rfl,
    show Assumptions.approx.localRule L g t pack208 = none from rfl,
    show Assumptions.mulBf16x2.localRule L g t pack208 = none from rfl,
    show Assumptions.cvtBf16x2.localRule L g t pack208 = none from rfl,
    show Assumptions.cvtUe8m0.localRule L g t pack208 = none from rfl,
    show Assumptions.lg2Exact.localRule L g t pack208 = none from rfl,
    show Assumptions.ncReadOnly.localRule L g t pack208 = none from rfl, hpar,
    show Assumptions.storeDrain.localRule L g t pack208 = none from rfl, hsh,
    show Assumptions.commitOrder.localRule L g t pack208 = none from rfl]
  cases Assumptions.deadPackRule L g t pack208 <;> rfl

/-- The pack writes the word with a zero high half. -/
theorem exec_pack208_ok {t : TState} (hpc : t.pc = 208) {v : Value}
    (h : t.regs 467 = some v) (h4 : v.bytes = 4) :
    execLocalA Assumptions.all L g t pack208 =
      .ok (PTX.next (setReg t 3144 (joinValue v (.bits 32 0)))) := by
  rw [execLocalA_208 hpc]
  have hd : Assumptions.deadPackWords t.pc = some (3144, 467, 950) := by rw [hpc]; rfl
  simp [Assumptions.deadPackRule, pack208, hd, readValue, readReg, h, h4, bind, Except.bind,
    pure, Except.pure]

/-- The `selp` of `%r18` (pc 244) on the predicate fact of pc 243. -/
theorem arrLSelp (c : Bool) {F : List (Nat × Value)} (hp : (75, Value.pred c) ∈ F)
    (hd : ∀ q ∈ F, q.1 ≠ 476) :
    Seg kernel Assumptions.all L g 1 244 F 245 ((476, w32 (sel c (i32 4) (i32 0))) :: F) :=
  Seg.selp_imm_eq (v := w32 (sel c (i32 4) (i32 0))) Flow.code_244 hp hd
    (by cases c <;> rfl)
    (fun t ht a ha => asms_localRule_int (by rw [ht]; decide) (by rw [ht]; decide)
      (by rw [ht]; decide) (Assumptions.peerPackRule_of_none (by rw [ht]; rfl)) a ha)

/-- The control stretch after the last-store arrival to the no-block test (pc 207). -/
theorem arrLSeg1 (d : Control.D) (x : BitVec 64) (sk : Value) :
    ∃ n, Seg kernel Assumptions.all L g n 201
      ((467, .bits 32 x) :: (2880, sk) :: factsFrom [465, 466, 473] (Control.valueOf P L g w d)) 207
      ((74, .pred (scmpi .lt .s (Control.r15 d.l0 d.l1) 64)) :: (467, .bits 32 x) :: (2880, sk) ::
        factsFrom [465, 466, 473] (Control.valueOf P L g w d)) := by
  seg_sym using w0_segS

/-- The scale pair's pack (pc 208), then the addresses of the staging rings up to the `selp`. -/
theorem arrLSeg2 (d : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 d.l0 d.l1) 64 = false) :
    ∃ n, Seg kernel Assumptions.all L g n 208
      ((74, .pred false) :: (467, .bits 32 x) :: (2880, sk) ::
        factsFrom [465, 466, 473] (Control.valueOf P L g w d)) 244
      ((75, .pred (scmpi .gt .s w 1)) :: (3243, scPair x) :: (467, .bits 32 x) :: (2880, sk) ::
        factsFrom [474, 988, 989, 990, 991, 992, 993, 994, 995, 996, 475, 2884, 465]
        (Control.valueOf P L g w (Control.loopEntry d))) := by
  refine Seg.comp_ex (q := 209)
    (H := (3144, joinValue (.bits 32 x) (.bits 32 0)) :: ((74, .pred false) ::
      (467, .bits 32 x) :: (2880, sk) :: factsFrom [465, 466, 473] (Control.valueOf P L g w d)))
    ⟨1, fun t ht => ?_⟩ ?_
  · obtain ⟨hpc, -, -, -, hF⟩ := id ht
    have h := hF.2.1
    have hfr : ∀ p ∈ ((74, Value.pred false) :: (467, Value.bits 32 x) :: (2880, sk) ::
        factsFrom [465, 466, 473] (Control.valueOf P L g w d)), p.1 ≠ 3144 := by
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | rfl | hp
      · decide
      · show (467 : Nat) ≠ 3144; decide
      · show (2880 : Nat) ≠ 3144; decide
      · exact Control.fresh_live (by decide) p hp
    exact ⟨_, run_local (op := pack208) Flow.code_208 rfl ht
      (exec_pack208_ok hpc h rfl), At.set ht hfr⟩
  simp only [Control.loopEntry, h74, Bool.false_eq_true, ↓reduceIte]
  dsimp only [scPair]
  seg_sym using w0_segS

/-- The rest of the set-up, from the `selp` on: the statistics' initial words and the barrier's
operands (pcs 245 to 255). -/
theorem arrLSeg3 (d : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 d.l0 d.l1) 64 = false) :
    ∃ n, Seg kernel Assumptions.all L g n 245
      ((476, w32 (sel (scmpi .gt .s w 1) (i32 4) (i32 0))) ::
        (75, .pred (scmpi .gt .s w 1)) :: (3243, scPair x) :: (467, .bits 32 x) :: (2880, sk) ::
        factsFrom [474, 988, 989, 990, 991, 992, 993, 994, 995, 996, 475, 2884, 465]
        (Control.valueOf P L g w (Control.loopEntry d))) 256
      ((467, .bits 32 x) :: (3243, scPair x) :: (2950, mI) :: (2955, lI) :: (2885, mxI) ::
        (2880, sk) :: factsFrom [76, 451, 452, 474, 475, 476, 972, 973, 988, 989, 990, 991, 992,
        993, 994, 995, 996, 2883, 2884, 2952, 2953]
        (Control.valueOf P L g w (Control.loopEntry d))) := by
  simp only [Control.loopEntry, h74, Bool.false_eq_true, ↓reduceIte]
  dsimp only [mI, lI, mxI, scPair]
  seg_sym using w0_segS

/-- The set-up with a block (pcs 201 to 255), over the facts it reads. -/
theorem arrLCoreF (d : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 d.l0 d.l1) 64 = false) :
    ∃ n, Seg kernel Assumptions.all L g n 201
      ((467, .bits 32 x) :: (2880, sk) :: factsFrom [465, 466, 473] (Control.valueOf P L g w d))
      256 ((467, .bits 32 x) :: (3243, scPair x) :: (2950, mI) :: (2955, lI) :: (2885, mxI) ::
        (2880, sk) :: factsFrom [76, 451, 452, 474, 475, 476, 972, 973, 988, 989, 990, 991, 992,
        993, 994, 995, 996, 2883, 2884, 2952, 2953]
        (Control.valueOf P L g w (Control.loopEntry d))) := by
  obtain ⟨n1, h1⟩ := arrLSeg1 (w := w) d x sk
  rw [h74] at h1
  have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (target := 1150)
    (p := 74) (uni := false) (pick := false) Flow.code_207
    (F := (74, .pred false) :: (467, .bits 32 x) :: (2880, sk) ::
      factsFrom [465, 466, 473] (Control.valueOf P L g w d)) (List.mem_cons_self ..)
    (fun t _ a ha => bra_rule t a ha) (w0SegFree 207)
  obtain ⟨n2, h2⟩ := arrLSeg2 (w := w) d x sk h74
  obtain ⟨n3, h3⟩ := arrLSeg3 (w := w) d x sk h74
  have hs := arrLSelp (L := L) (g := g) (scmpi .gt .s w 1)
    (F := (75, .pred (scmpi .gt .s w 1)) :: (3243, scPair x) :: (467, .bits 32 x) ::
      (2880, sk) :: factsFrom [474, 988, 989, 990, 991, 992, 993, 994, 995, 996, 475, 2884, 465]
      (Control.valueOf P L g w (Control.loopEntry d))) (List.mem_cons_self ..)
    (fun q hq => by
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | rfl | rfl | hq
      · show (75 : Nat) ≠ 476; omega
      · show (3243 : Nat) ≠ 476; omega
      · show (467 : Nat) ≠ 476; omega
      · show (2880 : Nat) ≠ 476; omega
      · exact Control.fresh_live (by decide) q hq)
  exact ⟨_, h1.comp (hb.comp (h2.comp (hs.comp h3)))⟩

/-- The set-up without a block, to the no-block test (pc 207). -/
theorem arrLSegT1 (d : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 d.l0 d.l1) 64 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 201
      ((467, .bits 32 x) :: (2880, sk) :: factsFrom [465, 466, 473] (Control.valueOf P L g w d))
      207 ((74, .pred true) :: (138, .pred true) :: (2950, mI) :: (2955, lI) ::
        (467, .bits 32 x) :: (2880, sk) :: (2953, w32 0) :: [(2954, w32 0)]) := by
  dsimp only [mI, lI]
  have h : ∃ n, Seg kernel Assumptions.all L g n 201
      ((467, .bits 32 x) :: (2880, sk) :: factsFrom [465, 466, 473] (Control.valueOf P L g w d))
      207 ((74, .pred (scmpi .lt .s (Control.r15 d.l0 d.l1) 64)) :: (138, .pred true) ::
        (2950, w32 (BitVec.ofNat 64 4048155338)) :: (2955, w32 (BitVec.ofNat 64 0)) ::
        (467, .bits 32 x) :: (2880, sk) :: (2953, w32 0) :: [(2954, w32 0)]) := by
    seg_sym using w0_segS
  rwa [h74] at h

/-- The epilogue's masked moves (pcs 1150 to 1153). -/
theorem arrLSegT2 (x : BitVec 64) (sk : Value) :
    ∃ n, Seg kernel Assumptions.all L g n 1150
      ((74, .pred true) :: (138, .pred true) :: (2950, mI) :: (2955, lI) ::
        (467, .bits 32 x) :: (2880, sk) :: (2953, w32 0) :: [(2954, w32 0)]) 1154
      ((138, .pred true) :: (481, w32 4286578688) :: (1727, w32 0) :: (2880, sk) ::
        (1725, w32 9) :: (1726, w32 128) :: (2953, w32 0) :: [(2954, w32 0)]) := by
  dsimp only [mI, lI]
  seg_sym using w0_segS

theorem arrL_lookup_off {a b : List (Nat × Value)} {r : Nat} (h : r ∉ a.map Prod.fst) :
    (a ++ b).lookup r = b.lookup r := by
  induction a with
  | nil => rfl
  | cons p a ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (r == k) = false := by simpa using h.1
    simp only [List.cons_append, List.lookup_cons, hne]
    exact ih h.2

/-- A register that neither state-dependent part of the value table names has the same value in
every state. -/
theorem arrL_valueOf_off {d d' : Control.D} {r : Nat}
    (h1 : r ∉ (Control.valuesLen d).map Prod.fst)
    (h2 : r ∉ (Control.valuesLoop L w d).map Prod.fst)
    (h3 : r ∉ (Control.valuesLen d').map Prod.fst)
    (h4 : r ∉ (Control.valuesLoop L w d').map Prod.fst) :
    Control.valueOf P L g w d r = Control.valueOf P L g w d' r := by
  simp only [Control.valueOf, Control.values, List.append_assoc]
  rw [arrL_lookup_off h1, arrL_lookup_off h2, arrL_lookup_off h3, arrL_lookup_off h4]

/-- The registers the set-up leaves alone (and the epilogue entry's), of the control table. -/
def arrLKeep : List Nat :=
  [459, 460, 463, 465, 469, 471, 472, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3001]

/-- The positions the set-up's two arms cross (the epilogue's masked moves included). -/
def arrLS : List Nat := List.range' 201 55 ++ [1150, 1151, 1152, 1153]

/-- The registers `arrLKeep` have the same value before and after the set-up. -/
theorem arrL_keep_eq (d d' : Control.D) : ∀ r ∈ arrLKeep,
    Control.valueOf P L g w d r = Control.valueOf P L g w d' r := by
  intro r hr
  simp only [arrLKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
  exact arrL_valueOf_off (by simp [Control.valuesLen]) (by simp [Control.valuesLoop])
    (by simp [Control.valuesLen]) (by simp [Control.valuesLoop])

/-- **The set-up with a block** (pcs 201 to 255) on the control table. -/
theorem arrLWinF (d : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 d.l0 d.l1) 64 = false) :
    ∃ n, Seg kernel Assumptions.all L g n 201
      (factsFrom (Control.ctlLive 200) (Control.valueOf P L g w d) ++ f_set x sk) 256
      (Control.facts P L g w (Control.loopEntry d) ++ f_car x mI lI mxI sk) := by
  obtain ⟨n, h⟩ := arrLCoreF (P := P) (L := L) (g := g) (w := w) d x sk h74
  have hf := Seg.frameSet (H := factsFrom arrLKeep (Control.valueOf P L g w d)) rulesFrame
    (S := arrLS) (by rw [factsFrom_keys]; kernel_rfl) (fun _ _ => w0SegFree _)
    (by kernel_rfl) h
  have hpc : (Control.loopEntry d).site.pc = 256 := by simp [Control.loopEntry, h74, Site.pc]
  refine ⟨n, (hf.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
  · obtain ⟨hc, hs⟩ := (holds_append _ _ _).mp hR
    obtain ⟨h1, h2, -⟩ := hs
    exact (holds_append _ _ _).mpr ⟨⟨h1, h2, holds_factsFrom_mono hc (by decide +kernel)⟩,
      holds_factsFrom_mono hc (by decide +kernel)⟩
  · obtain ⟨hE, hK⟩ := (holds_append _ _ _).mp hR
    have hK' : Holds R (factsFrom arrLKeep (Control.valueOf P L g w (Control.loopEntry d))) := by
      have : factsFrom arrLKeep (Control.valueOf P L g w d) =
          factsFrom arrLKeep (Control.valueOf P L g w (Control.loopEntry d)) := by
        unfold factsFrom
        exact List.map_congr_left fun r hr => by rw [arrL_keep_eq d _ r hr]
      rwa [this] at hK
    obtain ⟨h467, h3243, h2950, h2955, h2885, h2880, hW⟩ := hE
    have hall : Holds R (factsFrom ([76, 451, 452, 474, 475, 476, 972, 973, 988, 989, 990, 991,
        992, 993, 994, 995, 996, 2883, 2884, 2952, 2953] ++ arrLKeep)
        (Control.valueOf P L g w (Control.loopEntry d))) := by
      unfold factsFrom
      rw [List.map_append]
      exact (holds_append _ _ _).mpr ⟨hW, hK'⟩
    unfold Control.facts
    rw [hpc]
    exact (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hall (by decide +kernel),
      ⟨h467, h3243, h2950, h2955, h2885, h2880, trivial⟩⟩

/-- The registers of the empty entry's epilogue barrier, after the set-up. -/
theorem arrL_vals_T (d : Control.D) :
    Control.valueOf P L g w (Control.loopEntry d) 1725 = w32 9 ∧
    Control.valueOf P L g w (Control.loopEntry d) 1726 = w32 128 := by
  constructor <;>
  · simp only [Control.valueOf, Control.values, List.append_assoc]
    rw [arrL_lookup_off (by simp [Control.valuesLen]),
      arrL_lookup_off (by simp [Control.valuesLoop])]
    rfl

theorem arrL_vals_T2 (d : Control.D)
    (h74 : scmpi .lt .s (Control.r15 d.l0 d.l1) 64 = true) :
    Control.valueOf P L g w (Control.loopEntry d) 2953 = w32 0 ∧
    Control.valueOf P L g w (Control.loopEntry d) 2954 = w32 0 := by
  simp only [Control.loopEntry, h74, ↓reduceIte]
  constructor <;>
  · simp only [Control.valueOf, Control.values, List.append_assoc]
    rw [arrL_lookup_off (by simp [Control.valuesLen])]
    simp [Control.valuesLoop]
    rfl

/-- **The set-up without a block** (pcs 201 to 207 and 1150 to 1153) on the control table. -/
theorem arrLWinT (d : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 d.l0 d.l1) 64 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 201
      (factsFrom (Control.ctlLive 200) (Control.valueOf P L g w d) ++ f_set x sk) 1154
      (Control.facts P L g w (Control.loopEntry d) ++
        f_exit (lookupD (f_car x mI lI mxI sk))) := by
  obtain ⟨n1, h1⟩ := arrLSegT1 (P := P) (L := L) (g := g) (w := w) d x sk h74
  obtain ⟨n2, h2⟩ := arrLSegT2 (L := L) (g := g) x sk
  have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (target := 1150)
    (p := 74) (uni := false) (pick := true) Flow.code_207
    (F := (74, .pred true) :: (138, .pred true) :: (2950, mI) :: (2955, lI) ::
        (467, .bits 32 x) :: (2880, sk) :: (2953, w32 0) :: [(2954, w32 0)])
    (List.mem_cons_self ..) (fun t _ a ha => bra_rule t a ha) (w0SegFree 207)
  have h := h1.comp (hb.comp h2)
  have hf := Seg.frameSet (H := factsFrom arrLKeep (Control.valueOf P L g w d)) rulesFrame
    (S := arrLS) (by rw [factsFrom_keys]; kernel_rfl) (fun _ _ => w0SegFree _)
    (by kernel_rfl) h
  have hpc : (Control.loopEntry d).site.pc = 1154 := by simp [Control.loopEntry, h74, Site.pc]
  have hE : f_exit (lookupD (f_car x mI lI mxI sk)) =
      [(138, .pred true), (481, w32 4286578688), (1727, w32 0), (2880, sk)] := by kernel_rfl
  obtain ⟨v25, v26⟩ := arrL_vals_T (P := P) (L := L) (g := g) (w := w) d
  obtain ⟨v53, v54⟩ := arrL_vals_T2 (P := P) (L := L) (g := g) (w := w) d h74
  refine ⟨_, (hf.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
  · obtain ⟨hc, hs⟩ := (holds_append _ _ _).mp hR
    obtain ⟨h1, h2, -⟩ := hs
    exact (holds_append _ _ _).mpr ⟨⟨h1, h2, holds_factsFrom_mono hc (by decide +kernel)⟩,
      holds_factsFrom_mono hc (by decide +kernel)⟩
  · obtain ⟨hE', hK⟩ := (holds_append _ _ _).mp hR
    have hK' : Holds R (factsFrom arrLKeep (Control.valueOf P L g w (Control.loopEntry d))) := by
      have : factsFrom arrLKeep (Control.valueOf P L g w d) =
          factsFrom arrLKeep (Control.valueOf P L g w (Control.loopEntry d)) := by
        unfold factsFrom
        exact List.map_congr_left fun r hr => by rw [arrL_keep_eq d _ r hr]
      rwa [this] at hK
    obtain ⟨h138, h481, h1727, h2880, h1725, h1726, h2953, h2954, -⟩ := hE'
    have hn : Holds R (factsFrom [1725, 1726, 2953, 2954]
        (Control.valueOf P L g w (Control.loopEntry d))) := by
      refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · show R 1725 = some (Control.valueOf P L g w (Control.loopEntry d) 1725)
        rw [v25]; exact h1725
      · show R 1726 = some (Control.valueOf P L g w (Control.loopEntry d) 1726)
        rw [v26]; exact h1726
      · show R 2953 = some (Control.valueOf P L g w (Control.loopEntry d) 2953)
        rw [v53]; exact h2953
      · show R 2954 = some (Control.valueOf P L g w (Control.loopEntry d) 2954)
        rw [v54]; exact h2954
    have hall : Holds R (factsFrom (arrLKeep ++ [1725, 1726, 2953, 2954])
        (Control.valueOf P L g w (Control.loopEntry d))) := by
      unfold factsFrom
      rw [List.map_append]
      exact (holds_append _ _ _).mpr ⟨hK', hn⟩
    unfold Control.facts
    rw [hpc, hE]
    exact (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hall (by decide +kernel),
      ⟨h138, h481, h1727, h2880, trivial⟩⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
