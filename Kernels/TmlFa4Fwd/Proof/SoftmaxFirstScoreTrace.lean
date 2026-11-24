-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstGeometryReads
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Widen

import Lemmas.Step.TcLoad
public import Lemmas.Tcgen05.TcMmaSource
import Lemmas.Kernel.ProgressDescent
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

/-- The first scalar register written by a quarter of the first QK score load. -/
def scoreWordBase (quarter : Fin 4) : Nat :=
  #v[2881, 2914, 2946, 2979][quarter]

/-- The packed QK operand register holding the two score columns for a first-round pair. -/
def firstScorePairReg (quarter : Fin 4) (pair : Nat) : Nat :=
  7303 + 16*quarter.val + pair

private def scorePackInstr (quarter : Fin 4) (pair : Nat) : Instr :=
  ⟨none, .move ⟨.pack, .int .b 64, [some (firstScorePairReg quarter pair)],
    [.reg (scoreWordBase quarter+2*pair), .reg (scoreWordBase quarter+2*pair+1)]⟩⟩

private theorem scorePackSlice (quarter : Fin 4) :
    ((kernel.code.drop (scorePc .first quarter+1)).take 16) =
      (List.range 16).map (fun k => scorePackInstr quarter (15-k)) := by
  fin_cases quarter <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem scorePackCode (quarter : Fin 4) {n : Nat} (hn : n < 16) :
    kernel.code[scorePc .first quarter+1+(15-n)]? = some (scorePackInstr quarter n) := by
  have hi : 15-n < 16 := by omega
  have h := congrArg (fun es : List Instr => es[15-n]?) (scorePackSlice quarter)
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, show 15-(15-n) = n by omega] at h
  exact h

private theorem scorePackOff (quarter : Fin 4) {n : Nat} (hn : n < 16) :
    scorePc .first quarter+1+(15-n) ∉ Assumptions.swExp2Sites := by
  have hLo : 3428 ≤ scorePc .first quarter := by fin_cases quarter <;> decide
  have hHi : scorePc .first quarter ≤ 3481 := by fin_cases quarter <;> decide
  simp only [List.mem_cons, List.not_mem_nil, or_false, Assumptions.swExp2Sites]
  omega

private theorem scoreInputBelow (quarter : Fin 4) {word : Nat} (hw : word < 32) :
    scoreWordBase quarter + word < firstScorePairReg quarter 0 := by
  fin_cases quarter <;> simp [scoreWordBase, firstScorePairReg] <;> omega

private theorem runScorePack {l : Launch} {g : Nat} (quarter : Fin 4) {n : Nat}
    (hn : n ≤ 16) (words : Nat → Value) (hBytes : ∀ k < 32, (words k).bytes = 4)
    {t : TState} (ht : At t (scorePc .first quarter+1+(16-n)) [])
    (hWords : ∀ k < 32, t.regs (scoreWordBase quarter+k) = some (words k)) :
    ∃ u, run kernel Assumptions.all l g n t = some u ∧ At u (scorePc .first quarter+17) [] ∧
      (∀ k < n, u.regs (firstScorePairReg quarter k) =
        some (joinValue (words (2*k)) (words (2*k+1)))) ∧
      ∀ r, r < firstScorePairReg quarter 0 ∨ firstScorePairReg quarter n ≤ r →
        u.regs r = t.regs r := by
  induction n generalizing t with
  | zero =>
    refine ⟨t, rfl, ?_, fun k hk => (Nat.not_lt_zero _ hk).elim, fun _ _ => rfl⟩
    exact ⟨by rw [ht.1], ht.2⟩
  | succ n ih =>
    have hn' : n < 16 := by omega
    have hPC : scorePc .first quarter+1+(16-(n+1)) = scorePc .first quarter+1+(15-n) := by omega
    let dst := firstScorePairReg quarter n
    let value := joinValue (words (2*n)) (words (2*n+1))
    let v := next (setReg t dst value)
    have hv : run kernel Assumptions.all l g 1 t = some v := by
      apply run_local (scorePackCode quarter hn') rfl (hPC ▸ ht)
      rw [Assumptions.execLocalA_all_eq_numeric,
        Assumptions.execLocalA_eq_nil ((hPC ▸ ht).1.symm ▸ scorePackOff quarter hn') rfl]
      have hUpper : t.regs (scoreWordBase quarter+2*n+1) = some (words (2*n+1)) := by
        simpa only [Nat.add_assoc] using hWords (2*n+1) (by omega)
      have hExec := exec_pack (A := []) (L := l) (g := g) (d := dst) (by simp [NoPack])
        (hWords (2*n) (by omega)) hUpper Assumption.SegFreePc.nil
      rw [ite_eq_left ⟨hBytes (2*n) (by omega), hBytes (2*n+1) (by omega)⟩] at hExec
      exact hExec
    have hvAt : At v (scorePc .first quarter+1+(16-n)) [] := by
      have hs : At v ((scorePc .first quarter+1+(16-(n+1)))+1) [] :=
        (ht.set (r := dst) (v := value) (by simp)).mono trivial
      exact ⟨by rw [hs.1]; omega, hs.2⟩
    have hBack : ∀ r, r ≠ dst → v.regs r = t.regs r := by
      intro r hne
      exact Function.update_of_ne hne _ _
    have hDst : v.regs dst = some value := Function.update_self ..
    obtain ⟨u, hu, huAt, hPack, hFrame⟩ := ih (by omega) hvAt (by
      intro k hk
      have hlt := scoreInputBelow quarter hk
      exact (hBack _ (by dsimp [dst]; unfold firstScorePairReg at hlt ⊢; omega)).trans
        (hWords k hk))
    refine ⟨u, by simpa only [Nat.one_add] using run_comp hv hu, huAt, ?_, ?_⟩
    · intro k hk
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact (hFrame _ (.inr (Nat.le_refl _))).trans hDst
      · exact hPack k hlt
    · intro r hr
      have hBounds : r < firstScorePairReg quarter 0 ∨ dst < r := by
        unfold dst firstScorePairReg at *
        omega
      rcases hBounds with hLo | hHi
      · exact (hFrame r (.inl hLo)).trans
          (hBack r (by dsimp [dst]; unfold firstScorePairReg at hLo ⊢; omega))
      · exact (hFrame r (.inr hHi.le)).trans (hBack r (Nat.ne_of_gt hHi))

private def scoreWordRegs (quarter : Fin 4) : List Nat :=
  (List.range 32).map (scoreWordBase quarter + ·)

private theorem firstScoreCode (quarter : Fin 4) :
    kernel.code[scorePc .first quarter]? =
      some ⟨none, .tcLd (scoreWordRegs quarter) (scoreReg .first quarter) .s32x32b none⟩ := by
  fin_cases quarter
  · exact Flow.code_3428
  · exact Flow.code_3446
  · exact Flow.code_3463
  · exact Flow.code_3481

private theorem scoreWordsNodup (quarter : Fin 4) : (scoreWordRegs quarter).Nodup := by
  fin_cases quarter <;> decide

set_option maxRecDepth 10000 in
private theorem firstScoreOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (quarter : Fin 4) (stage : Fin 2) {g : Nat} {t : TState}
    (ht : At t (scorePc .first quarter)
      [(scoreReg .first quarter, b32 (scoreAddress l g stage quarter))]) :
    out kernel Assumptions.all l g t =
      .ev (.tcLd (scoreAddress l g stage quarter) 32 .s32x32b
        (setRegs (next t) (scoreWordRegs quarter))) := by
  have hCode := ht.1.symm ▸ firstScoreCode quarter
  have hStage := scoreColumn_range stage
  have hQuarter := quarter.isLt
  have hCol : scoreColumn stage+32*quarter.val < 512 := by omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hR := ht.2.2.2.2.1
  have hCore := tc_ld_supported (L := l) (g := g) (ds := scoreWordRegs quarter) (sh := .s32x32b)
    (by intro s h; cases h) hBlock hR (tmem_warp_encoding_lt l g hCol)
    (by simpa [scoreWordRegs] using (by decide : TcShape.s32x32b.countOk 32 = true))
    (tcDataAddressOk_warp32 l g hCol)
  rw [out_event ht.2.2.2.1 hCode rfl rfl]
  change Out.ev (tcLdTmpl Assumptions.all l g t _) = _
  have hHook := ht.1.symm ▸ scoreWaitHook .first quarter
  simp only [tcLdTmpl, hHook, hCore]
  simp [scoreWordRegs]

private theorem firstScoreQuarterPack {l : Launch} {g : Nat} (quarter : Fin 4)
    (stage : Fin 2) {t : TState} {vals : List Value}
    (ht : At t (scorePc .first quarter)
      [(scoreReg .first quarter, b32 (scoreAddress l g stage quarter))])
    (hLen : vals.length = 32) (hBytes : ∀ k < 32, (vals.getD k (b32 0)).bytes = 4) :
    ∃ u, At u (scorePc .first quarter+17) [] ∧
      (∀ k < 16, u.regs (firstScorePairReg quarter k) =
        some (joinValue (vals.getD (2*k) (b32 0)) (vals.getD (2*k+1) (b32 0)))) ∧
      (∀ r, (r < scoreWordBase quarter ∨ scoreWordBase quarter+32 ≤ r) →
        (r < firstScorePairReg quarter 0 ∨ firstScorePairReg quarter 16 ≤ r) →
        u.regs r = t.regs r) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g)
        (setRegs (next t) (scoreWordRegs quarter) vals) u := by
  have hLoad : ∀ k < 32, (setRegs (next t) (scoreWordRegs quarter) vals).regs
      (scoreWordBase quarter+k) = some (vals.getD k (b32 0)) := by
    intro k hk
    apply setRegs_get _ _ _ k _ _ (scoreWordsNodup quarter)
    · simp only [scoreWordRegs, List.getElem?_map, List.getElem?_range hk, Option.map_some]
    · have hIndex : k < vals.length := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIndex, Option.getD_some]
  have hS := setRegs_skel (next t) (scoreWordRegs quarter) vals
  have hStart : At (setRegs (next t) (scoreWordRegs quarter) vals)
      (scorePc .first quarter+1+(16-16)) [] :=
    ⟨hS.1.trans (congrArg (· + 1) ht.1), hS.2.1.trans ht.2.1,
      hS.2.2.1.trans ht.2.2.1, hS.2.2.2.trans ht.2.2.2.1, trivial⟩
  obtain ⟨u, hu, huAt, hPack, hFrame⟩ :=
    runScorePack quarter (Nat.le_refl 16) _ hBytes hStart hLoad
  refine ⟨u,huAt,hPack,?_,run_rtg hu⟩
  intro r hWord hPair
  have hNotMem : r ∉ scoreWordRegs quarter := by
    intro hMem
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hMem
    simp only [List.mem_range] at hk
    omega
  exact (hFrame r hPair).trans (setRegs_other _ _ _ _ hNotMem)

/-- Each first-round QK transfer writes its actual words into the decoded source registers.
The following sixteen packed operands have the ordering of the observed score columns. -/
theorem firstScoreQuarterTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (quarter : Fin 4) (stage : Fin 2) {g j : Nat} {t : TState}
    (ht : At t (scorePc .first quarter)
      [(scoreReg .first quarter, b32 (scoreAddress l g stage quarter))])
    (hBytes : ∀ vals, X.get (g, j) = some
      ⟨scorePc .first quarter, .tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u vals, vals.length = 32 ∧
      X.get (g, j) = some
        ⟨scorePc .first quarter, .tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      At u (scorePc .first quarter+17) [] ∧
      (∀ k < 16, u.regs (firstScorePairReg quarter k) =
        some (joinValue (vals.getD (2*k) (b32 0)) (vals.getD (2*k+1) (b32 0)))) ∧
      (∀ r, (r < scoreWordBase quarter ∨ scoreWordBase quarter+32 ≤ r) →
        (r < firstScorePairReg quarter 0 ∨ firstScorePairReg quarter 16 ≤ r) →
        u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+1)) none := by
  have hNext : Next kernel Assumptions.all l g t t
      (.tcLd (scoreAddress l g stage quarter) 32 .s32x32b
        (setRegs (next t) (scoreWordRegs quarter))) := ⟨.refl, firstScoreOut hp quarter stage ht⟩
  obtain ⟨_, _, he, ⟨vals, hLen, rfl, hsv⟩, hTail⟩ := hNext.continuing_at (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hr
  obtain rfl := Option.some.inj hsv
  rw [ht.1] at he
  obtain ⟨u,hU,hPack,hFrame,hLocal⟩ :=
    firstScoreQuarterPack quarter stage ht hLen (hBytes vals he)
  exact ⟨u,vals,hLen,he,hU,hPack,hFrame,hTail.after_local hLocal⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- At a released score-load cursor, a maximal trace records the decoded TMEM load.
Packing uses the full 32-bit returned words. Issuance and collective return are separate. -/
theorem firstScoreQuarterOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : TcMma.LayoutInjective X) {g j : Nat}
    (hg : g < l.threads) (quarter : Fin 4) (stage : Fin 2) {s t : TState} {ending : Option TState}
    (ht : At t (scorePc .first quarter)
      [(scoreReg .first quarter, b32 (scoreAddress l g stage quarter))])
    (hLastWords : ∀ k < 32, ∀ v, TcMma.LastWrote l Assumptions.all X
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) k) v → v.bytes = 4)
    (hBytes : ∀ vals, X.get (g,j) = some
      ⟨scorePc .first quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop j) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) (hPos : 0 < j)
    (hBound : j ≤ (X.tr g).length) (hRelease : j = (X.tr g).length → Step.Released l X g) :
    ∃ original u vals, vals.length = 32 ∧
      X.get (g,j) = some
        ⟨scorePc .first quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      At u (scorePc .first quarter+17) [] ∧
      (∀ k < 16, u.regs (firstScorePairReg quarter k) =
        some (joinValue (vals.getD (2*k) (b32 0)) (vals.getD (2*k+1) (b32 0)))) ∧
      (∀ r, (r < scoreWordBase quarter ∨ scoreWordBase quarter+32 ≤ r) →
        (r < firstScorePairReg quarter 0 ∨ firstScorePairReg quarter 16 ≤ r) →
        u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some original) ∧
      Run kernel Assumptions.all l g original ((X.tr g).drop (j+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) original u := by
  let addr := scoreAddress l g stage quarter
  let resume := setRegs (next t) (scoreWordRegs quarter)
  have hOut : out kernel Assumptions.all l g t = .ev (.tcLd addr 32 .s32x32b resume) :=
    firstScoreOut hp quarter stage ht
  have hn : Next kernel Assumptions.all l g s t (.tcLd addr 32 .s32x32b resume) :=
    ⟨hLocal,hOut⟩
  have hMore : j < (X.tr g).length := by
    by_contra! hStop
    have hEnd : j = (X.tr g).length := by omega
    have hStart : X.tr g ≠ [] := List.ne_nil_of_length_pos (hPos.trans_le hBound)
    have hFull : Run kernel Assumptions.all l g {} (X.tr g) (some s) := by
      simpa only [hEnd,List.take_length] using hPrefix
    let words := Step.loadVals l Assumptions.all X g .s32x32b addr 32
    have hStep : EStep kernel Assumptions.all l g t ⟨t.pc,.tc (.ld addr words .s32x32b)⟩
        (some (resume words)) :=
      ⟨_,hOut,words,Step.loadVals_length,rfl,rfl⟩
    exact hMax.not_grows (Step.tc_load_counted_extension hMax.1 hg hStart (hRelease hEnd)
      hFull hLocal hStep (fun k v hk hLast => by
        rw [Step.loadVals_length] at hk
        exact ⟨Step.loadVals_spec hMax.1 hGuard hLayout hk hLast,hLastWords k hk v hLast⟩)
      (Assumptions.wfStep _ _ hMax.1 le_snoc (Execution.notifiedInOrder_of_eq rfl)
        (Execution.noNewRead_snoc rfl)))
  obtain ⟨_, _, he, ⟨vals, hLen, rfl, hsv⟩, hRest⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hTail (fun hNil => Nat.not_le_of_lt hMore (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hsv
  have hFullStep : EStep kernel Assumptions.all l g t
      ⟨t.pc,.tc (.ld addr vals .s32x32b)⟩ (some (resume vals)) :=
    ⟨_,hOut,vals,hLen,rfl,rfl⟩
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1))
      (some (resume vals)) := by
    rw [List.take_succ_eq_append_getElem hMore, (List.getElem?_eq_some_iff.mp he).2]
    exact hPrefix.snoc hLocal hFullStep
  rw [ht.1] at he
  obtain ⟨u,hU,hPack,hFrame,hPackLocal⟩ :=
    firstScoreQuarterPack quarter stage ht hLen (hBytes vals he)
  exact ⟨_,u,vals,hLen,he,hU,hPack,hFrame,hPast,hRest,hPackLocal⟩

def nextScoreOrPc (site : Fin 2) : Nat := if site = 0 then 3445 else 3480

def nextScoreOrQuarter (site : Fin 2) : Fin 4 := if site = 0 then 1 else 3

private theorem nextScoreOrCode (site : Fin 2) :
    kernel.code[nextScoreOrPc site]? = some ⟨none, .int
      ⟨.or, .int .b 32, false, [some (scoreReg .first (nextScoreOrQuarter site))],
        [.reg 2788, .imm (32*(nextScoreOrQuarter site).val)]⟩⟩ := by
  fin_cases site
  · exact Flow.code_3445
  · exact Flow.code_3480

private theorem nextScoreOrExact {l : Launch} {g : Nat} (stage : Fin 2) (site : Fin 2)
    {t : TState} (ht : At t (nextScoreOrPc site)
      [(2788, b32 (scoreAddress l g stage 0))]) :
    Seg kernel Assumptions.all l g 1 (nextScoreOrPc site)
      [(2788, b32 (scoreAddress l g stage 0))]
      (scorePc .first (nextScoreOrQuarter site))
      [(scoreReg .first (nextScoreOrQuarter site),
        b32 (scoreAddress l g stage (nextScoreOrQuarter site)))] := by
  have hStage := scoreColumn_range stage
  have hWord := tmem_warp_encoding_lt l g (show scoreColumn stage < 512 by omega)
  have hMod : scoreAddress l g stage 0 < 2^32 := by
    simpa only [scoreAddress, Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hWord
  have hAlign : scoreAddress l g stage 0 = 2^7 * (512*laneBase l g+stage.val) := by
    simp only [scoreAddress, scoreColumn, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
    omega
  have hOr (quarter : Fin 4) : scoreAddress l g stage 0 ||| (32*quarter.val) =
      scoreAddress l g stage quarter := by
    have hQuarter := quarter.isLt
    rw [hAlign, ← Nat.two_pow_add_eq_or_of_lt (show 32*quarter.val < 2^7 by omega)]
    simp only [scoreAddress, scoreColumn]
    omega
  have hOr1 : scoreAddress l g stage 0 ||| 32 = scoreAddress l g stage 1 := hOr 1
  have hOr3 : scoreAddress l g stage 0 ||| 96 = scoreAddress l g stage 3 := hOr 3
  have hMod64 : scoreAddress l g stage 0 < 2^64 := by omega
  simp only [Nat.reducePow] at hMod hMod64
  fin_cases site
  · intro s hs
    change At s 3445 [(2788, b32 (scoreAddress l g stage 0))] at hs
    change ∃ u, _ ∧ At u 3446 [(2913, b32 (scoreAddress l g stage 1))]
    seg_fp hs using norm_bits [Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hMod64, hOr1]
  · intro s hs
    change At s 3480 [(2788, b32 (scoreAddress l g stage 0))] at hs
    change ∃ u, _ ∧ At u 3481 [(2978, b32 (scoreAddress l g stage 3))]
    seg_fp hs using norm_bits [Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hMod64, hOr3]

/-- The two intervening score address instructions select the next quarter of the tile. -/
theorem firstScoreOtherQuarter (l : Launch) (g : Nat) (stage : Fin 2) (late : Bool) :
    Seg kernel Assumptions.all l g 1 (if late then 3480 else 3445)
      [(2788, b32 (scoreAddress l g stage 0))]
      (scorePc .first (if late then 3 else 1))
      [(scoreReg .first (if late then 3 else 1), b32 (scoreAddress l g stage
        (if late then 3 else 1)))] := by
  intro t ht
  cases late
  · exact (nextScoreOrExact stage 0 ht).apply ht
  · exact (nextScoreOrExact stage 1 ht).apply ht

theorem nextScoreOrTrace {l : Launch} {g : Nat} (stage : Fin 2) (site : Fin 2)
    {t : TState} (ht : At t (nextScoreOrPc site)
      [(2788, b32 (scoreAddress l g stage 0))]) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (scorePc .first (nextScoreOrQuarter site))
        [(scoreReg .first (nextScoreOrQuarter site),
          b32 (scoreAddress l g stage (nextScoreOrQuarter site)))] ∧
      ∀ r, r ≠ scoreReg .first (nextScoreOrQuarter site) → u.regs r = t.regs r := by
  obtain ⟨u, hu, huAt⟩ := (nextScoreOrExact stage site ht).apply ht
  have hCode := nextScoreOrCode site
  have hOff : t.pc ∉ Assumptions.swExp2Sites := by
    rw [ht.1]
    fin_cases site <;> decide
  have hCore := Assumptions.tauStep_all_eq_nil (L := l) (g := g)
    hOff (ht.1.symm ▸ hCode) rfl
  have hStep : tauStep kernel [] l g t = some u := by
    cases h : tauStep kernel [] l g t with
    | none => simp [run, hCore, h] at hu
    | some w => simpa only [run, hCore, h, Option.bind_some] using hu
  refine ⟨u, hu, huAt, fun r hr => ?_⟩
  exact tau_core_regs (ht.1.symm ▸ hCode) (tauStep_iff.mp hStep) (by simpa [writesRegs] using hr)

/-- The stable registers exclude the decoded scalar and packed destinations of the four
first-round QK transfers and both local address writes. -/
def firstScoreKeeps (r : Nat) : Prop :=
  (r < 2881 ∨ 3011 ≤ r) ∧ (r < 7303 ∨ 7367 ≤ r)

private theorem scoreWordFrame (q : Fin 4) {r : Nat} (h : r < 2881 ∨ 3011 ≤ r) :
    r < scoreWordBase q ∨ scoreWordBase q+32 ≤ r := by
  have hLo : 2881 ≤ scoreWordBase q := by fin_cases q <;> decide
  have hHi : scoreWordBase q+32 ≤ 3011 := by fin_cases q <;> decide
  omega

private theorem scorePairFrame (q : Fin 4) {r : Nat} (h : r < 7303 ∨ 7367 ≤ r) :
    r < firstScorePairReg q 0 ∨ firstScorePairReg q 16 ≤ r := by
  have hLo : 7303 ≤ firstScorePairReg q 0 := by fin_cases q <;> decide
  have hHi : firstScorePairReg q 16 ≤ 7367 := by fin_cases q <;> decide
  omega

/-- Four score-load events and the corresponding packed operands before the bias wait. -/
def FirstScores (l : Launch) (X : Execution) (stage : Fin 2) (g j : Nat)
    (u : TState) (words : Fin 4 → List Value) : Prop :=
  (∀ q : Fin 4, (words q).length = 32 ∧
    X.get (g, j+q.val) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l g stage q) (words q) .s32x32b)⟩) ∧
  ∀ (q : Fin 4) (k : Nat), k < 16 → u.regs (firstScorePairReg q k) =
    some (joinValue ((words q).getD (2*k) (b32 0)) ((words q).getD (2*k+1) (b32 0)))

/-- Every first-round QK event occurs in quarter order. The words from those events are
the packed inputs at the first Bias-full poll. -/
theorem firstScoreTileTrace (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    (ht : At t 3428
      [(2788, b32 (scoreAddress l g stage 0)), (2789, b32 (scoreAddress l g stage 2))])
    (hBytes : ∀ (q : Fin 4) vals, X.get (g, j+q.val) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l g stage q) vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ (u : TState) (words : Fin 4 → List Value), At u 3498 [] ∧
      FirstScores l X stage g j u words ∧
      (∀ r, firstScoreKeeps r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+4)) none := by
  have hAddr0 := ht.2.2.2.2.1
  have hAddr2 := ht.2.2.2.2.2.1
  obtain ⟨u0, vals0, hLen0, hLoad0, hU0, hP0, hFrame0, hR0⟩ :=
    firstScoreQuarterTrace hp 0 stage (ht.mono ⟨hAddr0, trivial⟩) (hBytes 0) hr
  have hU0' : At u0 (nextScoreOrPc 0) [(2788, b32 (scoreAddress l g stage 0))] :=
    hU0.mono ⟨(hFrame0 _ (by decide) (by decide)).trans hAddr0, trivial⟩
  obtain ⟨v0, hv0, hV0, hMove0⟩ := nextScoreOrTrace stage 0 hU0'
  obtain ⟨u1, vals1, hLen1, hLoad1, hU1, hP1, hFrame1, hR1⟩ :=
    firstScoreQuarterTrace hp 1 stage hV0 (hBytes 1) (hR0.after_local (run_rtg hv0))
  have hAddr2' : u1.regs 2789 = some (b32 (scoreAddress l g stage 2)) :=
    (hFrame1 _ (by decide) (by decide)).trans ((hMove0 _ (by decide)).trans
      ((hFrame0 _ (by decide) (by decide)).trans hAddr2))
  have hU1' : At u1 (scorePc .first 2) [(scoreReg .first 2, b32 (scoreAddress l g stage 2))] :=
    hU1.mono ⟨hAddr2', trivial⟩
  obtain ⟨u2, vals2, hLen2, hLoad2, hU2, hP2, hFrame2, hR2⟩ :=
    firstScoreQuarterTrace hp 2 stage hU1' (hBytes 2) hR1
  have hAddr0' : u2.regs 2788 = some (b32 (scoreAddress l g stage 0)) :=
    (hFrame2 _ (by decide) (by decide)).trans ((hFrame1 _ (by decide) (by decide)).trans
      ((hMove0 _ (by decide)).trans ((hFrame0 _ (by decide) (by decide)).trans hAddr0)))
  have hU2' : At u2 (nextScoreOrPc 1) [(2788, b32 (scoreAddress l g stage 0))] :=
    hU2.mono ⟨hAddr0', trivial⟩
  obtain ⟨v2, hv2, hV2, hMove2⟩ := nextScoreOrTrace stage 1 hU2'
  obtain ⟨u3, vals3, hLen3, hLoad3, hU3, hP3, hFrame3, hR3⟩ :=
    firstScoreQuarterTrace hp 3 stage hV2 (hBytes 3) (hR2.after_local (run_rtg hv2))
  let values (q : Fin 4) : List Value := #v[vals0, vals1, vals2, vals3][q]
  refine ⟨u3, values, hU3, ⟨?_, ?_⟩, ?_, hR3⟩
  · intro q
    fin_cases q
    · exact ⟨hLen0, hLoad0⟩
    · exact ⟨hLen1, hLoad1⟩
    · exact ⟨hLen2, hLoad2⟩
    · exact ⟨hLen3, hLoad3⟩
  · intro q k hk
    have hWord (other : Fin 4) : scoreWordBase other+32 ≤ firstScorePairReg q k := by
      have hUpper : scoreWordBase other+32 ≤ 3011 := by fin_cases other <;> decide
      unfold firstScorePairReg
      omega
    have hPair (other : Fin 4) (hlt : q.val < other.val) :
        firstScorePairReg q k < firstScorePairReg other 0 := by
      unfold firstScorePairReg
      omega
    have hReg : 7303 ≤ firstScorePairReg q k := by unfold firstScorePairReg; omega
    fin_cases q
    · exact (hFrame3 _ (.inr (hWord 3)) (.inl (hPair 3 (by decide)))).trans
        ((hMove2 _ (by change _ ≠ 2978; omega)).trans
          ((hFrame2 _ (.inr (hWord 2)) (.inl (hPair 2 (by decide)))).trans
            ((hFrame1 _ (.inr (hWord 1)) (.inl (hPair 1 (by decide)))).trans
              ((hMove0 _ (by change _ ≠ 2913; omega)).trans (hP0 k hk)))))
    · exact (hFrame3 _ (.inr (hWord 3)) (.inl (hPair 3 (by decide)))).trans
        ((hMove2 _ (by change _ ≠ 2978; omega)).trans
          ((hFrame2 _ (.inr (hWord 2)) (.inl (hPair 2 (by decide)))).trans (hP1 k hk)))
    · exact (hFrame3 _ (.inr (hWord 3)) (.inl (hPair 3 (by decide)))).trans
        ((hMove2 _ (by change _ ≠ 2978; omega)).trans (hP2 k hk))
    · exact hP3 k hk
  · intro r hKeep
    obtain ⟨hWord, hPair⟩ := hKeep
    exact (hFrame3 r (scoreWordFrame 3 hWord) (scorePairFrame 3 hPair)).trans
      ((hMove2 r (by change r ≠ 2978; omega)).trans
        ((hFrame2 r (scoreWordFrame 2 hWord) (scorePairFrame 2 hPair)).trans
          ((hFrame1 r (scoreWordFrame 1 hWord) (scorePairFrame 1 hPair)).trans
            ((hMove0 r (by change r ≠ 2913; omega)).trans
              (hFrame0 r (scoreWordFrame 0 hWord) (scorePairFrame 0 hPair))))))

private theorem firstScoreFactsFrame {R S : Nat → Option Value} {F : List (Nat × Value)}
    (hF : Holds R F) (hRegs : ∀ r, firstScoreKeeps r → S r = R r)
    (hKeep : ∀ x ∈ F, firstScoreKeeps x.1) : Holds S F := by
  induction F with
  | nil => trivial
  | cons x F ih =>
    obtain ⟨r, v⟩ := x
    exact ⟨(hRegs r (hKeep (r, v) (by simp))).trans hF.1,
      ih hF.2 (fun x hx => hKeep x (List.mem_cons_of_mem _ hx))⟩

/-- The first QK-full wait is followed by the four score loads and packs. All selected
live registers, including the fetched geometry, are available at Bias-full. -/
theorem firstQkScoreTileTrace (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    {F : List (Nat × Value)} (ht : At t 3425 F) (hWait : (2769, b32 (waitLoc l g stage 1).addr) ∈ F)
    (hPhase : (2770, b32 0) ∈ F) (hAddr0 : (2788, b32 (scoreAddress l g stage 0)) ∈ F)
    (hAddr2 : (2789, b32 (scoreAddress l g stage 2)) ∈ F)
    (hKeep : ∀ x ∈ F, x.1 ≠ 9751 ∧ firstScoreKeeps x.1)
    (hBytes : ∀ pos (q : Fin 4) vals, X.get (g, pos) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l g stage q) vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ (fails : Nat) (u : TState) (words : Fin 4 → List Value),
      let start := j+fails+1
      (X.tr g).drop j =
        List.replicate fails ⟨3425, .wait (waitLoc l g stage 1) 0 false true .cta⟩ ++
          ⟨3425, .wait (waitLoc l g stage 1) 0 true true .cta⟩ :: (X.tr g).drop start ∧
      At u 3498 F ∧ FirstScores l X stage g start u words ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+4)) none := by
  obtain ⟨fails, v, hEvents, hv, hvRun⟩ :=
    waitTraceAt hp stage 1 g 0 (by decide) hWait hPhase (fun x hx => (hKeep x hx).1) ht hr
  have hvAt : At v 3428
      [(2788, b32 (scoreAddress l g stage 0)), (2789, b32 (scoreAddress l g stage 2))] :=
    hv.mono ⟨holds_mem hv.2.2.2.2 hAddr0, holds_mem hv.2.2.2.2 hAddr2, trivial⟩
  obtain ⟨u, words, huAt, hWords, hFrame, huRun⟩ :=
    firstScoreTileTrace hp stage hvAt (fun q => hBytes _ q) hvRun
  refine ⟨fails, u, words, hEvents, huAt.mono ?_, hWords, huRun⟩
  exact firstScoreFactsFrame hv.2.2.2.2 hFrame (fun x hx => (hKeep x hx).2)

end PTX.Kernels.TmlFa4Fwd.Softmax
