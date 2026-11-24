-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CountedVisits
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.ExitPrefix
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.MmaRoleSetup
public import Kernels.TmlFa4Fwd.Proof.MmaScanPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Mma

noncomputable section

private theorem countBeforeMonotone {a b : Nat} (h : a ≤ b) (visits : List Visit) :
    countedUntil a visits ≤ countedUntil b visits := by
  induction visits with
  | nil => exact le_rfl
  | cons v vs ih =>
    by_cases ha : v.pc < a
    · have hb : v.pc < b := by omega
      cases he : v.ev with
      | none => simpa [countedUntil, ha, hb, List.filterMap_cons, he] using ih
      | some e =>
        simpa [countedUntil, ha, hb, List.filterMap_cons, he, List.countP_cons] using
          Nat.add_le_add_right ih (if e.counts then 1 else 0)
    · simp [countedUntil, ha]

private theorem epilogueSegmentBound (i : Fin 6) {l : Launch} {g n m : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {F : List (Nat × Value)}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hl : (epilogueRegion i).lo ≤ s.pc) (hh : s.pc < (epilogueRegion i).hi)
    (hAt : At s s.pc F) (hKeep : ∀ pair ∈ F, pair.1 ∈ epilogueBoundsFrame i)
    (hPrefix : countedUntil (epilogueRegion i).hi vs ≤ n)
    (hSuffix : ∀ {u rest tail}, u.pc ∈ (epilogueRegion i).exits → At u u.pc F →
      Walk kernel Assumptions.all l g u rest tail → countedUntil 9206 tail ≤ m) :
    countedUntil 9206 vs ≤ n + m := by
  let P := fun t : TState => t.sub = 0 ∧ t.acc = [] ∧ Holds t.regs F
  have hStep {t u : TState} {e : Option Event}
      (hLo : (epilogueRegion i).lo ≤ t.pc) (hHi : t.pc < (epilogueRegion i).hi)
      (he : WStep kernel Assumptions.all l g t e u) (ht : P t) :
      ((epilogueRegion i).lo ≤ u.pc ∧ u.pc < (epilogueRegion i).hi ∨
        u.pc ∈ (epilogueRegion i).exits ∧ u.fault = none) ∧ P u := by
    obtain ⟨hPc, hs, ha, hf⟩ := epilogueIntervalStep i hLo hHi ht.1 ht.2.1 he
    exact ⟨hPc, hs, ha, holdsSchedulerFrame ht.2.2 hf hKeep⟩
  have hInit : P s := ⟨hAt.2.1, hAt.2.2.1, hAt.2.2.2.2⟩
  rcases cutWalkInterval (cutoff := 9206) hw hl hh hInit (by fin_cases i <;> decide)
    hStep with hb | ⟨u, rest, tail, he, hf, hR, hW, hb⟩
  · omega
  · have ht : At u u.pc F := ⟨rfl, hR.1, hR.2.1, hf, hR.2.2⟩
    have hCount := hSuffix he ht hW
    omega

private def warpFact : List (Nat × Value) := [(1062, b32 13)]

private theorem postDrainBound {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : At s 3086 warpFact) : countedUntil 9206 vs ≤ 33 := by
  have hPrefix : countedUntil 3099 vs ≤ 32 := by
    apply (countBeforeMonotone (show 3099 ≤ (linearRegionBounds 6).2 by decide) vs).trans
    exact linearRolePrefixBound 6 hw (by rw [hs.1]; decide)
      (by rw [hs.2.1]; decide) hs.2.2.1
  have hAt : At s s.pc warpFact := ⟨rfl, hs.2⟩
  apply epilogueSegmentBound (n := 32) (m := 1) 5 hw hs.1.ge (by rw [hs.1]; decide)
    hAt (by simp [warpFact, epilogueBoundsFrame]) hPrefix
  intro u rest tail he hu hW
  have hp : u.pc = 3099 := by simpa [epilogueRegion] using he
  exact sharedExitPrefixBound hW hp hu.2.2.2.1 (.inr rfl) hu.2.2.2.2.1

private def groupBudget (p : Params) := 64 * (p.batch + 1)

private theorem drainScanBound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta : Nat} (hCta : cta + 1 < 2 ^ 31) {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : At s 3032 (groupScanFacts .epilogueDrain 0 p.batch cta))
    (hWarp : s.regs 1062 = some (b32 13)) : countedUntil 9206 vs ≤ groupBudget p + 33 := by
  have hb : p.batch + 31 < 2 ^ 31 := by have := hp.shape.2.2.2.2.2; omega
  have hPrefix : countedUntil 3086 vs ≤ groupBudget p := by
    change countedUntil ((scanSite .epilogueDrain).compare + 3) vs ≤ groupBudget p
    simpa only [groupBudget, Nat.sub_zero] using
      groupScanPrefixBound .epilogueDrain hb hCta (Nat.zero_le _) hs hw
  have hAt : At s s.pc warpFact := ⟨rfl, hs.2.1, hs.2.2.1, hs.2.2.2.1, hWarp, trivial⟩
  apply epilogueSegmentBound (m := 33) 4 hw hs.1.ge (by rw [hs.1]; decide)
    hAt (by simp [warpFact, epilogueBoundsFrame]) hPrefix
  intro u rest tail he hu hW
  have huPc : u.pc = 3086 := by simpa [epilogueRegion] using he
  exact postDrainBound hW ⟨huPc, hu.2⟩

private theorem setupCut (i : Fin 4) {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : s.pc = (epilogueSetupSpan i).1) :
    countedUntil 9206 vs ≤ 1 ∨
      ∃ u tail, run kernel Assumptions.all l g ((epilogueSetupSpan i).2 -
        (epilogueSetupSpan i).1) s = some u ∧ u.pc = (epilogueSetupSpan i).2 ∧
        Walk kernel Assumptions.all l g u es tail ∧
        countedUntil 9206 vs ≤ countedUntil 9206 tail := by
  have hHi : (epilogueSetupSpan i).1 ≤ (epilogueSetupSpan i).2 := by fin_cases i <;> decide
  rcases cutWalkFallthrough (cutoff := 9206) hw hp.ge (hp ▸ hHi)
    (epilogueSetupStep i) with hb | ⟨u, tail, hu, hPc, hW, hCt⟩
  · exact .inl hb
  · exact .inr ⟨u, tail, by simpa only [hp] using hu, hPc, hW, hCt⟩

private theorem setupFromRun {l : Launch} {g cta batch : Nat} (scan : GroupScan)
    (hCta : cta + 1 < 2 ^ 31) {s u : TState} (i : Fin 4)
    (hL : (epilogueSetupSpan i).1 = (scanSite scan).head - 3)
    (hN : (epilogueSetupSpan i).2 - (epilogueSetupSpan i).1 = 3)
    (hC : (scanSite scan).cta = 1072)
    (hAt : At s (epilogueSetupSpan i).1
      [(1072, b32 cta), ((scanSite scan).batch, b32 batch), (1062, b32 13)])
    (hr : run kernel Assumptions.all l g
      ((epilogueSetupSpan i).2 - (epilogueSetupSpan i).1) s = some u) :
    At u (scanSite scan).head (groupScanFacts scan 0 batch cta) ∧
      u.regs 1062 = some (b32 13) := by
  have hA : At s ((scanSite scan).head - 3)
      [((scanSite scan).cta, b32 cta), ((scanSite scan).batch, b32 batch)] := by
    rw [hC]
    exact ⟨hAt.1.trans hL, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1,
      hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, trivial⟩
  have hRun : run kernel Assumptions.all l g 3 s = some u := hN ▸ hr
  have hv := groupInitFromRun scan hCta hA hRun
  refine ⟨hv, ?_⟩
  have hFrame := epilogueSetupRegisters i hAt.1.ge (by rw [hAt.1]; omega) hr
  exact hFrame.2.1.trans hAt.2.2.2.2.2.2.1

private def selectFacts (p : Params) (cta : Nat) : List (Nat × Value) :=
  [(1072, b32 cta), (7228, b32 p.batch), (1062, b32 13)]

private def drainFacts (p : Params) (cta : Nat) : List (Nat × Value) :=
  [(1072, b32 cta), (7147, b32 p.batch), (1062, b32 13)]

def commonCountFacts (cta : Nat) : List (Nat × Value) :=
  [(1072, b32 cta), (1062, b32 13)]

private theorem batchLoad {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta : Nat} {s u : TState} (initial : Bool)
    (hAt : At s (if initial then 2768 else 2949) (commonCountFacts cta))
    (hRun : run kernel Assumptions.all l g 1 s = some u) :
    At u (if initial then 2769 else 2950)
      (if initial then selectFacts p cta else drainFacts p cta) := by
  obtain ⟨hBound, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [param19_name] at hParam
  let dest := if initial then 7228 else 7147
  let v := next (setReg s dest (b32 p.batch))
  have hExec : run kernel [] l g 1 s = some v := by
    cases initial
    · apply run_local Flow.code_2949 rfl hAt
      rw [execLocalA_nil, execLocal_mem rfl]
      simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
        DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBound (by decide)]
      rfl
    · apply run_local Flow.code_2768 rfl hAt
      rw [execLocalA_nil, execLocal_mem rfl]
      simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
        DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBound (by decide)]
      rfl
  have hPc : 2768 ≤ s.pc ∧ s.pc ≤ 3100 := by
    rw [hAt.1]
    cases initial <;> decide
  have hActual : run kernel Assumptions.all l g 1 s = some v := by
    simp only [run, tauStep, epilogue_out_all_eq_nil (.inl hPc)] at hExec ⊢
    exact hExec
  rw [hRun] at hActual
  obtain rfl := Option.some.inj hActual
  have hC := hAt.2.2.2.2.1
  have hW := hAt.2.2.2.2.2.1
  cases initial <;> simp [At, selectFacts, drainFacts, v, next, setReg, dest,
    hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, hC, hW]

section
variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g cta : Nat}
    (hCta : cta + 1 < 2 ^ 31) {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
include hp hCta hw

private theorem boundWithDrainSetup (ht : At s 3029 (drainFacts p cta)) :
    countedUntil 9206 vs ≤ groupBudget p + 33 := by
  rcases setupCut 3 hw ht.1 with hb | ⟨u, tail, hr, _, hW, hCt⟩
  · omega
  · obtain ⟨hu, hw⟩ := setupFromRun .epilogueDrain hCta 3 rfl rfl rfl ht hr
    exact hCt.trans (drainScanBound hp hCta hW hu hw)

private theorem linearDrainBound (ht : At s 2950 (drainFacts p cta)) :
    countedUntil 9206 vs ≤ groupBudget p + 400 := by
  have hPrefix : countedUntil 3029 vs ≤ 310 := by
    apply (countBeforeMonotone (show 3029 ≤ (linearRegionBounds 5).2 by decide) vs).trans
    exact linearRolePrefixBound 5 hw (by rw [ht.1]; decide)
      (by rw [ht.2.1]; decide) ht.2.2.1
  have hb := epilogueSegmentBound (n := 310) (m := groupBudget p + 33) 3 hw ht.1.ge
    (by rw [ht.1]; decide) ⟨rfl, ht.2⟩
    (by simp [drainFacts, epilogueBoundsFrame]) hPrefix (by
      intro u rest tail he hu hW
      have h : u.pc = 3029 ∨ u.pc = 3086 := by simpa [epilogueRegion] using he
      rcases h with hp' | hp'
      · exact boundWithDrainSetup hp hCta hW ⟨hp', hu.2⟩
      · have hAt : At u 3086 warpFact := by
          exact ⟨hp', hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.2.2.1, trivial⟩
        exact (postDrainBound hW hAt).trans (by omega))
  omega

private theorem beforeDrainBound (ht : At s 2949 (commonCountFacts cta)) :
    countedUntil 9206 vs ≤ groupBudget p + 400 := by
  rcases setupCut 2 hw ht.1 with h | ⟨u, tail, hr, _, hW, hCt⟩
  · omega
  · exact hCt.trans (linearDrainBound hp hCta hW (batchLoad hp false ht hr))

set_option maxRecDepth 3000 in
private theorem linearOutputBound (ht : At s 2878 (commonCountFacts cta)) :
    countedUntil 9206 vs ≤ groupBudget p + 800 := by
  have hPrefix : countedUntil 2949 vs ≤ 310 := by
    apply (countBeforeMonotone (show 2949 ≤ (linearRegionBounds 5).2 by decide) vs).trans
    exact linearRolePrefixBound 5 hw (by rw [ht.1]; decide)
      (by rw [ht.2.1]; decide) ht.2.2.1
  have hb := epilogueSegmentBound (n := 310) (m := groupBudget p + 400) 2 hw ht.1.ge
    (by rw [ht.1]; decide) ⟨rfl, ht.2⟩
    (by simp [commonCountFacts, epilogueBoundsFrame]) hPrefix (by
      intro u rest tail he hu hW
      have h : u.pc = 2949 ∨ u.pc = 3099 := by simpa [epilogueRegion] using he
      rcases h with hp' | hp'
      · exact beforeDrainBound hp hCta hW ⟨hp', hu.2⟩
      · exact (sharedExitPrefixBound hW hp' hu.2.2.2.1 (.inr rfl) hu.2.2.2.2.2.1).trans (by omega))
  omega

set_option maxRecDepth 3000 in
private theorem selectScanBound (hs : At s 2824 (groupScanFacts .epilogueSelect 0 p.batch cta))
    (hWarp : s.regs 1062 = some (b32 13)) : countedUntil 9206 vs ≤ 2 * groupBudget p + 800 := by
  have hb : p.batch + 31 < 2 ^ 31 := by have := hp.shape.2.2.2.2.2; omega
  have hPrefix : countedUntil 2878 vs ≤ groupBudget p := by
    change countedUntil ((scanSite .epilogueSelect).compare + 3) vs ≤ groupBudget p
    simpa only [groupBudget, Nat.sub_zero] using
      groupScanPrefixBound .epilogueSelect hb hCta (Nat.zero_le _) hs hw
  have hAt : At s s.pc (commonCountFacts cta) := by
    exact ⟨rfl, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2.2.2.1, hWarp, trivial⟩
  have hBound := epilogueSegmentBound (m := groupBudget p + 800) 1 hw hs.1.ge
    (by rw [hs.1]; decide) hAt (by simp [commonCountFacts, epilogueBoundsFrame]) hPrefix (by
      intro u rest tail he hu hW
      have huPc : u.pc = 2878 := by simpa [epilogueRegion] using he
      exact linearOutputBound hp hCta hW ⟨huPc, hu.2⟩)
  omega

set_option maxRecDepth 3000 in
/-- The complete warp-13 role reaches at most a fixed straight-line count plus two request
group scans. Arbitrary execution prefixes may stop before a load, poll, or exit. -/
theorem epilogueRolePrefixBound (ht : At s 2768 (commonCountFacts cta)) :
    countedUntil 9206 vs ≤ 128 * (p.batch + 1) + 1000 := by
  rcases setupCut 0 hw ht.1 with h | ⟨u, tail, hr, _, hW, hCt⟩
  · omega
  have hu := batchLoad hp true ht hr
  have hPrefix : countedUntil 2821 tail ≤ 114 := by
    apply (countBeforeMonotone (show 2821 ≤ (linearRegionBounds 4).2 by decide) tail).trans
    exact linearRolePrefixBound 4 hW (by rw [hu.1]; decide)
      (by rw [hu.2.1]; decide) hu.2.2.1
  have hb := epilogueSegmentBound (n := 114) (m := 2 * groupBudget p + 800) 0 hW hu.1.ge
    (by rw [hu.1]; decide) ⟨rfl, hu.2⟩
    (by simp [selectFacts, epilogueBoundsFrame]) hPrefix (by
      intro v rest suffix he hv hS
      have h : v.pc = 2821 ∨ v.pc = 2878 := by simpa [epilogueRegion] using he
      rcases h with hp' | hp'
      · rcases setupCut 1 hS hp' with hb | ⟨w, endTrace, hInit, _, hEnd, hCount⟩
        · omega
        · obtain ⟨ht, hw⟩ := setupFromRun .epilogueSelect hCta 1 rfl rfl rfl ⟨hp', hv.2⟩ hInit
          exact hCount.trans (selectScanBound hp hCta hEnd ht hw)
      · have hAt : At v 2878 (commonCountFacts cta) := by
          exact ⟨hp', hv.2.1, hv.2.2.1, hv.2.2.2.1,
            hv.2.2.2.2.1, hv.2.2.2.2.2.2.1, trivial⟩
        exact (linearOutputBound hp hCta hS hAt).trans (by omega))
  unfold groupBudget at hb
  omega
end

/-- The warp-13 count starts at the actual common-barrier continuation and includes its return. -/
theorem epilogueRolePrefixFromDispatch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : At s 174 [(1062, b32 13), (2535, b32 l.sharedBase)]) :
    es.countP Event.counts ≤ 128 * (p.batch + 1) + 1001 := by
  obtain ⟨u, hr, hu⟩ := Prologue.dispatchRunFromCommon hp 13 hg hs
  have hGrid : g / l.block < l.grid :=
    (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCta : g / l.block + 1 < 2 ^ 31 :=
    (Nat.succ_le_of_lt hGrid).trans_lt hp.grid.2.2
  rcases advanceWalkLocals hr hw with he | ⟨tail, _, hCount, hw'⟩
  · subst es
    simp
  · have hAt : At u 2768 (commonCountFacts (g / l.block)) :=
      ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.2.1, hu.2.2.2.2.1, trivial⟩
    have hPrefix := (hCount 9206).trans (epilogueRolePrefixBound hp hCta hw' hAt)
    have hAll := countedThroughCode hw
    rw [Decoded.code_length] at hAll
    omega

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
