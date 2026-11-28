-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictSmr
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.DeadPack
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.ExitWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.FacWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.SegLib
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepEld
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepSink
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepVote
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSites2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.StepS0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.StepS1
public import Lemmas.Flow.SegFrameSet
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part001
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part009

@[expose] public section

/-! # The conditions of warpgroup 0's strict windows

`WinCond L g d e`: for each site whose window runs arithmetic that can fault, the condition the
window's strict step (`sk_<pc>`) takes, for the state `d` and the event `e`. The field `w<pc>` is
the hypothesis of `sk_<pc>` as an implication on the site. -/

/-! # The strict step of the `setmaxnreg` (pc 103)

The window to the next site is exact (`smrSegS`); the successor may leave the block's chain (the
batch is over), where the data machine states no facts (`skW_nxg`). -/

/-! # The strict step of the rescale fence (pc 711)

The window after the fence: the pack of the scale factor (pc 712, exact when the factor is a
four-byte word) and the factor pair's run (`Gen.alpha_run`), framed over the control facts. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The pack at pc 712 writes the factor with a zero high half when the factor is a word. -/
theorem exec_pack712_ok {t : TState} (hpc : t.pc = 712) {v : Value} (h : t.regs 2951 = some v)
    (h4 : v.bytes = 4) :
    execLocalA Assumptions.all L g t pack712 =
      .ok (PTX.next (setReg t 3565 (joinValue v (.bits 32 0)))) := by
  rw [execLocalA_712 hpc]
  have hd : Assumptions.deadPackWords t.pc = some (3565, 2951, 1715) := by rw [hpc]; rfl
  simp [Assumptions.deadPackRule, pack712, hd, readValue, readReg, h, h4, bind, Except.bind,
    pure, Except.pure]

/-- **The strict pack at pc 712**, for a factor that is a word. -/
theorem segS_712 (L : Launch) (g : Nat) (V : Nat → Value) (hb : (V 2951).bytes = 4) :
    ∃ n, Seg kernel Assumptions.all L g n 712
      (factsFrom [2951, 467, 3243, 2950, 2955, 2885, 2880] V) 713
      ((3565, joinValue (V 2951) (.bits 32 0)) ::
        factsFrom [2951, 467, 3243, 2950, 2955, 2885, 2880] V) := by
  refine ⟨1, fun t ht => ?_⟩
  obtain ⟨hpc, -, -, -, hF⟩ := id ht
  have h := holds_mem hF (mem_factsFrom (show 2951 ∈ [2951, 467, 3243, 2950, 2955, 2885, 2880]
    by decide))
  exact ⟨_, run_local (op := pack712) Flow.code_712 rfl ht (exec_pack712_ok hpc h hb),
    At.set ht (not_mem_factsFrom (by decide))⟩

/-- The factor pair's run, with the constant it moves into register 1263 (a control constant)
kept among its facts. -/
theorem alphaS (L : Launch) (g : Nat) (V : Nat → Value) :
    SegD kernel Assumptions.all L g 3 713 (Gen.alpha_facts0 V) 716
      [(1263, Gen.alpha_v715 V), (3312, Gen.alpha_v714 V)] (Gen.alpha_cond V) :=
  SegD.outs_lit (items := Gen.alpha_items0)
    ⟨⟨XItem.codeB_of Flow.code_713 rfl, w0SegFree 713, XItem.core_sink (w0SegFree 713)
          (noRuleW0 713 rfl) rfl⟩,
     ⟨XItem.codeB_of Flow.code_714 rfl, w0SegFree 714, rule_move 714 rfl⟩,
     ⟨XItem.codeB_of Flow.code_715 rfl, w0SegFree 715, XItem.core_mov (w0SegFree 715)
         (noRuleW0 (op := Gen.alpha_op715) 715 rfl) rfl⟩,
     trivial⟩
    rfl (by kernel_rfl) rfl (by kernel_rfl) (by kernel_rfl)

/-- The condition of the window after the fence. -/
def rsfCond (x : BitVec 64) (b : Blk) : Prop :=
  (lookupD (f_fin x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3)
    (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt) 2951).bytes = 4 ∧
  Gen.alpha_cond (lookupD (f_a0 x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
    (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt))

/-- The window of the fence, over the data facts alone; it ends with the constant moved into
register 1263. -/
theorem rsfWinS (L : Launch) (g : Nat) (x : BitVec 64) (m l mx sk : Value) (lo hi : List Value)
    (mw : Value) (p0 p1 p2 p3 p4 p5 p6 p7 : Value × Value) (pm : Value) (vt : Bool)
    (hb : (lookupD (f_fin x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt) 2951).bytes = 4)
    (c : Gen.alpha_cond (lookupD (f_a0 x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt))) :
    ∃ n, Seg kernel Assumptions.all L g n 712
      (f_fin x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt) 716
      ((1263, Gen.alpha_v715 (lookupD (f_a0 x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt))) ::
        f_blk x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt) := by
  obtain ⟨n1, h1⟩ := segS_712 L g (lookupD (f_ost x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7
    pm vt)) hb
  refine ⟨n1 + _, h1.comp ((SegD.frame (H := (f_fin x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7
      pm vt)) rulesFrame
      (alphaS L g (lookupD (f_a0 x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt)))
      rfl (by kernel_rfl) (by kernel_rfl) fun _ _ => w0SegFree _).seg c)⟩

/-- The constant register 1263 after the fence's window is the control machine's value. -/
theorem alpha_v715_eq (V : Nat → Value) (c : Control.D) :
    Gen.alpha_v715 V = Control.valueOf P L g w { c with site := .rld 0 } 1263 := by
  simp only [Gen.alpha_v715]
  rfl

/-- **The strict step at pc 711** (the rescale fence), under the window's condition. -/
theorem sk_711 (d : D) (hs : d.c.site = .rsf) (hok : d.ok = true) (hc : rsfCond (scX L) d.b)
    (e : Event) : (code P L g w).StepFor d e := by
  refine skW_nx (pc := 711) (pc' := 716) (by rw [hs]; rfl) rfl
    (c' := { d.c with site := .rld 0 }) (b' := d.b) (by rw [hs]; decide)
    (by rw [hs]; exact Flow.code_711)
    (fun {t e u} hf => by
      rw [hs] at hf
      exact Code.fires_tcPlain_next (.inl rfl) hf) (by rw [hs]; decide) hok
    (fun e => by simp [Control.succ, hs]) (by simp [succOk, hs])
    (fun _ => by simp [record, hs]) (fun h => h)
    (fun h => by simp [Control.elems, h]) ?_ e
  obtain ⟨n, h⟩ := rsfWinS L g (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
    (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) d.b.pm d.b.vt
    hc.1 hc.2
  have h3 := Seg.frameSet (H := factsFrom ((Control.ctlLive 716).erase 1263)
    (Control.valueOf P L g w { d.c with site := .rld 0 })) rulesFrame
    (S := [712, 713, 714, 715]) (by rw [factsFrom_keys]; kernel_rfl) (fun _ _ => w0SegFree _)
    (by kernel_rfl) h
  have e1 : wF (scX L) d.c.site d.b = f_fin (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi
      d.b.mw (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
      (d.b.pw 7) d.b.pm d.b.vt := by rw [hs]; rfl
  have e2 : wF (scX L) (Site.rld 0) d.b = f_blk (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi
      d.b.mw (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
      (d.b.pw 7) d.b.pm d.b.vt := rfl
  refine ⟨n, (h3.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
  · rw [e1] at hR
    have hs' := (holds_append _ _ _).mp hR
    refine (holds_append _ _ _).mpr ⟨hs'.2, facts_sub_erase (c := d.c)
      (c' := { d.c with site := .rld 0 }) rfl (fun q hq => ?_) R hs'.1⟩
    have hl : ∀ q ∈ (Control.ctlLive 716).erase 1263, q ∈ Control.ctlLive 711 := by
      decide +kernel
    have hp : d.c.site.pc = 711 := by rw [hs]; rfl
    rw [hp]
    exact hl q hq
  · rw [e2]
    have hs' := (holds_append _ _ _).mp hR
    have h4 := facts_of_erase (P := P) (L := L) (g := g) (w := w)
      (c := { d.c with site := .rld 0 }) (r := 1263) (R := R)
      (by show 1263 ∈ Control.ctlLive 716; decide +kernel)
      (by rw [← alpha_v715_eq (P := P) (L := L) (g := g) (w := w) _ d.c]; exact hs'.1.1) hs'.2
    exact (holds_append _ _ _).mpr ⟨h4, hs'.1.2⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- **An event that continues at the next instruction**, whether or not the successor is on the
chain (the data facts are those of the chain's successor, else none). -/
theorem skW_nxg {d : D} {c' : Control.D} {ins0 : Instr} {b' : Blk} {pc pc' : Nat}
    (hp : d.c.site.pc = pc) (hp' : c'.site.pc = pc') (hna : d.c.site ≠ .arrS)
    (hc : kernel.code[d.c.site.pc]? = some ins0)
    (hadv : ∀ {t e u}, Fires d.c.site.pc (eventTmpl Assumptions.all L g t ins0.op) e (some u) →
      u = PTX.next t)
    (hel1 : Control.elems d.c.site = 1) (hok : d.ok = true)
    (hsucc : ∀ e, Control.succ P L g w d.c e = some (some c'))
    (hrec : ∀ e, record d.c e d.b = b')
    (he1 : d.c.el = 0 → c'.el = 0)
    (hel : d.c.el = 0 → c'.el < Control.elems c'.site)
    (hseg : ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) pc'
      (Control.facts P L g w c' ++ if succOk d.c c' = true then wF (scX L) c'.site b' else []))
    (e : Event) : (code P L g w).StepFor d e := by
  by_cases hso : succOk d.c c' = true
  · simp only [hso, ↓reduceIte] at hseg
    exact skW_nx hp hp' hna hc hadv hel1 hok hsucc hso hrec he1 hel hseg e
  · have hso' : succOk d.c c' = false := by simpa using hso
    simp only [hso, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hseg
    have hn : ∀ e, (code P L g w).next d e = some (some ⟨c', b', d.hist, false⟩) := by
      intro e
      show (Control.succ P L g w d.c e).map _ = _
      rw [hsucc e]
      show some (some (dataNext L d c' e)) = _
      rw [dataNext_eq hna, hrec e, hso']
      simp [hok]
    intro ins hat hi hc' hf
    have he0 := el0_of_one hel1 hi
    refine (Code.step_issue (C := code P L g w) (dn := ⟨c', b', d.hist, false⟩) hc hadv
      (fun e => ?_) (by exact he0)
      (by simp [Control.D.acc, he0]) ?_).step ins hat hi hc' hf
    · rw [hn e]
    · refine ⟨fun _ => ?_, he1 he0, by simp [Control.D.acc, he1 he0], fun _ => hel he0⟩
      show ∃ n, Seg _ _ _ _ _ (d.c.site.pc + 1) _ c'.site.pc _
      rw [hp, hp']
      have hf0 : (code P L g w).facts d =
          Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b := facts_ok hok
      rw [hf0]
      exact hseg.imp fun n h => h.weaken_end fun R hR => by
        show Holds R (Control.facts P L g w c' ++ dF L ⟨c', b', d.hist, false⟩)
        simp only [dF, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        exact hR

/-- The window's end facts, restated as the step asks (on the chain or off it). -/
theorem smr_end {d : D} {c' : Control.D} {b' : Blk} {R : Nat → Option Value}
    (hw : succOk d.c c' = true → wF (scX L) c'.site b' = Control.smrData L)
    (hR : Holds R (Control.facts P L g w c' ++ Control.smrData L)) :
    Holds R (Control.facts P L g w c' ++
      if succOk d.c c' = true then wF (scX L) c'.site b' else []) := by
  by_cases hso : succOk d.c c' = true
  · simp only [hso, ↓reduceIte, hw hso]
    exact hR
  · simp only [hso, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ((holds_append _ _ _).mp hR).1

/-- **The strict step at pc 103** (the `setmaxnreg`), for a thread that is launched. -/
theorem sk_103 (hp : Pre P L m) (hg : g < L.threads ∧ g / L.block < L.grid) (d : D)
    (hs : d.c.site = .smr) (hok : d.ok = true) (e : Event) :
    (code P L g w).StepFor d e := by
  have hp103 : d.c.site.pc = 103 := by rw [hs]; rfl
  have hw : succOk d.c (Control.afterSmr P L g w d.c) = true →
      wF (scX L) (Control.afterSmr P L g w d.c).site { d.b with sk := mxI } =
        Control.smrData L := by
    intro h
    simp only [succOk, hs, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> rw [h] <;> rfl
  have hw0 : wF (scX L) d.c.site d.b = [] := by rw [hs]; rfl
  have key : ∀ e, (code P L g w).StepFor d e := by
    refine skW_nxg (pc := 103) (pc' := (Control.afterSmr P L g w d.c).site.pc)
      (c' := Control.afterSmr P L g w d.c) (b' := { d.b with sk := mxI }) hp103 rfl
      (by rw [hs]; decide) (by rw [hs]; exact Flow.code_103)
      (fun {t e u} hf => by rw [hs] at hf; exact Control.fires_smr_next hf) (by rw [hs]; rfl) hok
      (fun e => by simp [Control.succ, hs]) (fun e => by simp [record, hs])
      (fun h => by rw [Control.afterSmr_el (P := P) (L := L) (g := g) (w := w)]; exact h)
      (fun h => by
        rw [Control.afterSmr_el (P := P) (L := L) (g := g) (w := w), h]
        exact Control.elems_pos _) ?_
    obtain ⟨n, h⟩ := Control.smrSegS (w := w) hp hg d.c
    generalize Control.afterSmr P L g w d.c = c' at h hw ⊢
    refine ⟨n, (h.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
    · rw [hw0, List.append_nil] at hR
      unfold Control.facts at hR
      rw [hp103] at hR
      exact hR
    · exact smr_end hw hR
  exact fun {t u} => key e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

structure WinCond (L : Launch) (g : Nat) (d : D) (e : Event) : Prop where
  /-- pc 156. -/
  w156 : d.c.site = .sink →
    ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y) ∧ Gen.sk_cond (lookupD
    (s_sink (scX L) d.b.sk (.bits 32 y)))
  /-- pc 289. -/
  w289 : d.c.site = (.vm) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (Gen.mask_cond (lookupD (s_vm (scX
    L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (v)))) ∧ (Gen.pk394_cond (lookupD
    (m_vm (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (v))))
  /-- pc 403. -/
  w403 : d.c.site = (.pst 0) →
    Gen.pk404_cond (lookupD (f_pst0 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 413. -/
  w413 : d.c.site = (.pst 1) →
    Gen.pk414_cond (lookupD (f_pst1 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 423. -/
  w423 : d.c.site = (.pst 2) →
    Gen.pk424_cond (lookupD (f_pst2 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 433. -/
  w433 : d.c.site = (.pst 3) →
    Gen.pk434_cond (lookupD (f_pst3 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 443. -/
  w443 : d.c.site = (.pst 4) →
    Gen.pk444_cond (lookupD (f_pst4 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 453. -/
  w453 : d.c.site = (.pst 5) →
    Gen.pk454_cond (lookupD (f_pst5 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 463. -/
  w463 : d.c.site = (.pst 6) →
    Gen.pk464_cond (lookupD (f_pst6 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 475. -/
  w475 : d.c.site = (.bar1) →
    Gen.pk476_cond (lookupD (f_pst7 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw)))
  /-- pc 477. -/
  w477 : d.c.site = (.pld 0) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum0_cond (lookupD
    (s_pld0 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.c.a0, v))))
  /-- pc 482. -/
  w482 : d.c.site = (.pld 1) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum1_cond (lookupD
    (s_pld1 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
    (d.c.a0, v))))
  /-- pc 487. -/
  w487 : d.c.site = (.pld 2) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum2_cond (lookupD
    (s_pld2 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
    (d.b.pw 1) (d.c.a0, v))))
  /-- pc 492. -/
  w492 : d.c.site = (.pld 3) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum3_cond (lookupD
    (s_pld3 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
    (d.b.pw 1) (d.b.pw 2) (d.c.a0, v))))
  /-- pc 497. -/
  w497 : d.c.site = (.pld 4) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum4_cond (lookupD
    (s_pld4 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
    (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.c.a0, v))))
  /-- pc 502. -/
  w502 : d.c.site = (.pld 5) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum5_cond (lookupD
    (s_pld5 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
    (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.c.a0, v))))
  /-- pc 507. -/
  w507 : d.c.site = (.pld 6) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum6_cond (lookupD
    (s_pld6 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
    (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.c.a0, v))))
  /-- pc 512. -/
  w512 : d.c.site = (.pld 7) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → (Gen.sum7_cond
    (lookupD (s_pld7 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw)
    (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.c.a0, v))))
    ∧ (Gen.rmax_cond (lookupD (f_pld8 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo)
    (d.b.hi) (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw
    6) (d.c.a0, v)))))
  /-- pc 572. -/
  w572 : d.c.site = (.mld) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ Gen.mld_cond (lookupD (s_mld (scX L)
    (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw
    2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) (v)))
  /-- pc 578. -/
  w578 : d.c.site = .vote →
    ∀ m p r, e.kind = .voteMode .any m p r → voteCond (scX L) d.b r
  /-- pc 711. -/
  w711 : d.c.site = .rsf →
    rsfCond (scX L) d.b
  /-- pc 717. -/
  w717 : d.c.site = (.rldw 0) →
    Gen.rs0_cond (lookupD (f_rldw0 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o)))
  /-- pc 818. -/
  w818 : d.c.site = (.rldw 1) →
    Gen.rs1_cond (lookupD (f_rldw1 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o)))
  /-- pc 919. -/
  w919 : d.c.site = (.rldw 2) →
    Gen.rs2_cond (lookupD (f_rldw2 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o)))
  /-- pc 1020. -/
  w1020 : d.c.site = (.rldw 3) →
    Gen.rs3_cond (lookupD (f_rldw3 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o)))
  /-- pc 1122. -/
  w1122 : d.c.site = .arrS →
    scmpi .ne .b (Control.advance d.c).cnt 1 = false → exitCond L d.c d.b
  /-- pc 1157. -/
  w1157 : d.c.site = .eld →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ eldCond (L := L) (g := g) d.b v
  /-- pc 1187. -/
  w1187 : d.c.site = .efa →
    facCond (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe
  /-- pc 1202. -/
  w1202 : d.c.site = (.oldw 0) →
    Gen.es0_cond (lookupD (f_ow 0 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o)))
  /-- pc 1362. -/
  w1362 : d.c.site = (.oldw 1) →
    Gen.es1_cond (lookupD (f_ow 1 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o)))
  /-- pc 1520. -/
  w1520 : d.c.site = (.oldw 2) →
    Gen.es2_cond (lookupD (f_ow 2 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o)))
  /-- pc 1677. -/
  w1677 : d.c.site = (.oldw 3) →
    Gen.es3_cond (lookupD (f_ow 3 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o)))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
