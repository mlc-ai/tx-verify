-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaRoleSetup
public import Kernels.TmlFa4Fwd.Proof.MmaScanPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

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

private theorem phaseLinearBound {hi budget : Nat} (i : Fin 4) {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hLo : (linearBounds i).1 ≤ s.pc) (hHi : hi ≤ (linearBounds i).2)
    (hs : RoleShape s) (hb : 2 * ((linearBounds i).2 - (linearBounds i).1) + 2 ≤ budget) :
    countedUntil hi vs ≤ budget :=
  (countBeforeMonotone hHi vs).trans ((mmaLinearPrefixBound i hw hLo hs.1 hs.2.1).trans hb)

private def ctaReg (cta : Nat) (s : TState) : Prop := s.regs 1072 = some (b32 cta)

private def batchReg (reg batch : Nat) (s : TState) : Prop := s.regs reg = some (b32 batch)

private theorem preserveCta (region : Fin 12) {l : Launch} {g cta : Nat} {s u : TState}
    {e : Option Event}
    (hl : (roleRegion region).lo ≤ s.pc) (hh : s.pc < (roleRegion region).hi)
    (he : WStep kernel Assumptions.all l g s e u) (hs : ctaReg cta s) : ctaReg cta u :=
  (mmaStepCta (by fin_cases region <;> simp [roleRegion] at hl <;> omega)
    (by fin_cases region <;> simp [roleRegion] at hh <;> omega) he).trans hs

private theorem preserveBatch {lo hi reg batch : Nat} {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hRole : 1904 ≤ lo ∧ hi ≤ 2768)
    (hCode : ((kernel.code.drop lo).take (hi - lo)).all
      (fun op => !(mmaWrites op.op).contains reg) = true)
    (hl : lo ≤ s.pc) (hh : s.pc < hi) (he : WStep kernel Assumptions.all l g s e u)
    (hs : batchReg reg batch s) : batchReg reg batch u := by
  have h := mmaStepReg (r := reg) (by omega) (by omega) (h := he)
  apply (h ?_).trans hs
  intro ins hc
  have hh' : ((kernel.code.drop lo).take (hi - lo))[s.pc - lo]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hl]
    exact hc
  simpa using List.all_eq_true.mp hCode ins (List.mem_of_getElem? hh')

private theorem shapeAt {s : TState} {pc : Nat} {F : List (Nat × Value)}
    (hp : s.pc = pc) (h : RoleShape s) (hf : s.fault = none) (hpc : pc ≠ 1909)
    (hF : Holds s.regs F) : At s pc F :=
  ⟨hp, h.2.2 (fun h' => hpc (hp.symm.trans h')), h.2.1, hf, hF⟩

private theorem atShape {s : TState} {pc : Nat} {F : List (Nat × Value)} (h : At s pc F) :
    RoleShape s :=
  ⟨by rw [h.2.1]; decide, h.2.2.1, fun _ => h.2.1⟩

private theorem boundRegion (region : Fin 12) {l : Launch} {g n m : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {P : TState → Prop}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hl : (roleRegion region).lo ≤ s.pc) (hh : s.pc < (roleRegion region).hi)
    (hs : RoleShape s) (hP : P s)
    (hKeep : ∀ {v u : TState} {e : Option Event},
      (roleRegion region).lo ≤ v.pc → v.pc < (roleRegion region).hi →
      WStep kernel Assumptions.all l g v e u → P v → P u)
    (hPrefix : countedUntil (roleRegion region).hi vs ≤ n)
    (hSuffix : ∀ {u rest tail}, u.pc ∈ (roleRegion region).exits → u.fault = none →
      RoleShape u → P u → Walk kernel Assumptions.all l g u rest tail →
      countedUntil 2768 tail ≤ m) :
    countedUntil 2768 vs ≤ n + m := by
  rcases cutMmaRegion region hw hl hh hs hP hKeep with hc | ⟨v, rest, tail, he, hf, hv, hp, ht, hc⟩
  · omega
  · have hh := hSuffix he hf hv hp ht
    omega

private theorem boundSilent (region : Fin 12) (hSilent : 8 ≤ region.val)
    {l : Launch} {g budget : Nat} {s : TState} {es : List Event} {vs : List Visit}
    {P : TState → Prop} (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : s.pc = (roleRegion region).lo) (hs : RoleShape s) (hP : P s)
    (hKeep : ∀ {v u : TState} {e : Option Event},
      (roleRegion region).lo ≤ v.pc → v.pc < (roleRegion region).hi →
      WStep kernel Assumptions.all l g v e u → P v → P u)
    (hSuffix : ∀ {u rest tail},
      run kernel Assumptions.all l g ((roleRegion region).hi - (roleRegion region).lo) s = some u →
      u.pc = (roleRegion region).hi → u.fault = none → RoleShape u → P u →
      Walk kernel Assumptions.all l g u rest tail → countedUntil 2768 tail ≤ budget) :
    countedUntil 2768 vs ≤ 1 + budget := by
  rcases cutMmaSilent region hSilent hw hPc hs hP hKeep with
    h | ⟨v, rest, tail, hv, he, hf, hs, hp, hw, h⟩
  · omega
  · have hh := hSuffix hv he hf hs hp hw
    omega

private def groupsBudget (p : Params) : Nat := 64 * (p.batch + 1)

private def mmaTripsBudget : Nat := 1099511627776

private theorem mmaTripsBudget_eq : mmaTripsBudget = 256 * 2 ^ 32 := by decide

private theorem finishBound {l : Launch} {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hPc : 2750 ≤ s.pc) (hs : RoleShape s) :
    countedUntil 2768 vs ≤ 38 :=
  phaseLinearBound (hi := 2768) 3 hw hPc (by decide) hs (by decide)

section
variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
variable {g cta : Nat} (hCta : cta + 1 < 2 ^ 31)
include hp hCta

section
variable {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
include hw

private theorem drainScanBound (hs : At s 2696 (groupScanFacts .drain 0 p.batch cta)) :
    countedUntil 2768 vs ≤ groupsBudget p + 38 := by
  have hPrefix : countedUntil 2750 vs ≤ groupsBudget p := by
    change countedUntil ((scanSite .drain).compare + 3) vs ≤ groupsBudget p
    simpa only [groupsBudget, Nat.sub_zero] using
      groupScanPrefixBound .drain (by have := hp.shape.2.2.2.2.2; omega) hCta (Nat.zero_le _) hs hw
  apply boundRegion (P := fun _ => True) 6 hw hs.1.ge (by rw [hs.1]; decide) (atShape hs) trivial
    (fun _ _ _ _ => trivial) hPrefix
  intro u rest tail he _ hu _ hW
  have hPc : u.pc = 2750 := by simpa [roleRegion] using he
  exact finishBound hW hPc.ge hu

private theorem drainSetupBound (hs : At s 2693 [(1072, b32 cta), (7149, b32 p.batch)]) :
    countedUntil 2768 vs ≤ groupsBudget p + 39 := by
  have hb := boundSilent (P := fun _ => True) 10 (by decide)
    hw hs.1 (atShape hs) trivial (fun _ _ _ _ => trivial)
    (budget := groupsBudget p + 38) (fun hr _ _ _ _ hW =>
      drainScanBound hp hCta hW (groupInitFromRun .drain hCta hs hr))
  simpa only [Nat.add_left_comm 1, Nat.reduceAdd] using hb

private theorem drainPrepBound (hs : At s 2648 [(7149, b32 p.batch), (1072, b32 cta)]) :
    countedUntil 2768 vs ≤ groupsBudget p + 365 := by
  have hNoWrite : ((kernel.code.drop 2648).take (2693 - 2648)).all
      (fun i => !(mmaWrites i.op).contains 7149) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hKeep {v u : TState} {e : Option Event} (hl : 2648 ≤ v.pc) (hh : v.pc < 2693)
      (he : WStep kernel Assumptions.all l g v e u)
      (h : ctaReg cta v ∧ batchReg 7149 p.batch v) :
      ctaReg cta u ∧ batchReg 7149 p.batch u :=
    ⟨preserveCta 5 hl hh he h.1, preserveBatch (by decide) hNoWrite hl hh he h.2⟩
  have hPrefix := phaseLinearBound (hi := 2693) (budget := 326) 2 hw
    (by rw [hs.1]; decide) (by decide) (atShape hs) (by decide)
  have hb := boundRegion 5 hw hs.1.ge (by rw [hs.1]; decide) (atShape hs)
    (show ctaReg cta s ∧ batchReg 7149 p.batch s from ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.1⟩)
    hKeep hPrefix (m := groupsBudget p + 39) (by
      intro u rest tail he hf hu ⟨hCTA, hBatch⟩ hW
      have hE : u.pc = 2693 ∨ u.pc = 2750 := by simpa [roleRegion] using he
      rcases hE with ha | hb
      · exact drainSetupBound hp hCta hW (shapeAt ha hu hf (by decide) ⟨hCTA, hBatch, trivial⟩)
      · exact (finishBound hW hb.ge hu).trans (by omega))
  simpa only [Nat.add_left_comm 326, Nat.reduceAdd] using hb

private theorem drainLoadBound (hs : At s 2647 [(1072, b32 cta)]) :
    countedUntil 2768 vs ≤ groupsBudget p + 366 := by
  have hb := boundSilent (P := fun _ => True) 11 (by decide) hw hs.1
    (atShape hs) trivial (fun _ _ _ _ => trivial) (budget := groupsBudget p + 365)
    (fun hr _ _ _ _ hW => drainPrepBound hp hCta hW (drainBatchFromRun hp hs hr))
  simpa only [Nat.add_left_comm 1, Nat.reduceAdd] using hb

private theorem tailBound (hPc : s.pc = 2534) (hs : RoleShape s) (hc : ctaReg cta s) :
    countedUntil 2768 vs ≤ groupsBudget p + 692 := by
  have hPrefix := phaseLinearBound (hi := 2647) (budget := 326) 2 hw hPc.ge
    (by decide) hs (by decide)
  have hb := boundRegion 4 hw hPc.ge (by rw [hPc]; decide) hs hc (preserveCta 4) hPrefix
    (m := groupsBudget p + 366) (by
      intro u rest tail he hf hu hC hW
      have hP : u.pc = 2647 := by simpa [roleRegion] using he
      exact drainLoadBound hp hCta hW (shapeAt hP hu hf (by decide) ⟨hC, trivial⟩))
  simpa only [Nat.add_left_comm 326, Nat.reduceAdd] using hb

omit hw in
private theorem steadyBound {s : TState} {es : List Event} {vs : List Visit} (word : Nat)
    (hWord : word < 2 ^ 32) (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : At s 2291 [(7204, b32 word)]) (hC : ctaReg cta s) :
    countedUntil 2768 vs ≤ mmaTripsBudget + groupsBudget p + 692 := by
  have hPrefix : countedUntil 2534 vs ≤ mmaTripsBudget := by
    rw [mmaTripsBudget_eq]
    exact steadyLoopPrefixUniform hw hWord hs
  have hb := boundRegion 3 hw hs.1.ge (by rw [hs.1]; decide) (atShape hs) hC
    (preserveCta 3) hPrefix (m := groupsBudget p + 692) (by
      intro u rest tail he hf hu hC hW
      have hP : u.pc = 2534 := by simpa [roleRegion] using he
      exact tailBound hp hCta hW hP hu hC)
  simpa only [Nat.add_assoc] using hb

private theorem tripSetupBound (hPc : s.pc = 2286) (hs : RoleShape s) (hc : ctaReg cta s) :
    countedUntil 2768 vs ≤ mmaTripsBudget + groupsBudget p + 693 := by
  have hb := boundSilent 9 (by decide) hw hPc hs hc (preserveCta 9)
    (budget := mmaTripsBudget + groupsBudget p + 692) (by
      intro u rest tail hr hP hf hu hC hW
      obtain ⟨_, word, hw, hReg⟩ := initializedCounterWord hPc hr
      exact steadyBound hp hCta word hw hW (shapeAt hP hu hf (by decide) ⟨hReg, trivial⟩) hC)
  simpa only [Nat.add_left_comm 1, Nat.reduceAdd] using hb

private theorem selectedBound (hPc : s.pc = 2042) (hs : RoleShape s) (hc : ctaReg cta s) :
    countedUntil 2768 vs ≤ mmaTripsBudget + groupsBudget p + 1193 := by
  have hPrefix := phaseLinearBound (hi := 2286) (budget := 500) 1 hw hPc.ge
    (by decide) hs (by decide)
  have hb := boundRegion 2 hw hPc.ge (by rw [hPc]; decide) hs hc (preserveCta 2) hPrefix
    (m := mmaTripsBudget + groupsBudget p + 693) (by
      intro u rest tail he hf hu hC hW
      have hP : u.pc = 2286 ∨ u.pc = 2534 ∨ u.pc = 2763 := by simpa [roleRegion] using he
      rcases hP with hP | hP | hP
      · exact tripSetupBound hp hCta hW hP hu hC
      · exact (tailBound hp hCta hW hP hu hC).trans (by omega)
      · exact (finishBound hW (by omega) hu).trans (by omega))
  simpa only [Nat.add_left_comm 500, Nat.reduceAdd] using hb

private theorem firstScanBound (hs : At s 1988 (groupScanFacts .select 0 p.batch cta)) :
    countedUntil 2768 vs ≤ mmaTripsBudget + 2 * groupsBudget p + 1193 := by
  have hPrefix : countedUntil 2042 vs ≤ groupsBudget p := by
    change countedUntil ((scanSite .select).compare + 3) vs ≤ groupsBudget p
    simpa only [groupsBudget, Nat.sub_zero] using
      groupScanPrefixBound .select (by have := hp.shape.2.2.2.2.2; omega) hCta (Nat.zero_le _) hs hw
  have hCTA : ctaReg cta s := hs.2.2.2.2.2.2.2.1
  have hb := boundRegion 1 hw hs.1.ge (by rw [hs.1]; decide) (atShape hs) hCTA
    (preserveCta 1) hPrefix (m := mmaTripsBudget + groupsBudget p + 1193) (by
      intro u rest tail he hf hu hC hW
      have hP : u.pc = 2042 := by simpa [roleRegion] using he
      exact selectedBound hp hCta hW hP hu hC)
  simpa only [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

private theorem firstSetupBound (hs : At s 1985 [(1072, b32 cta), (7203, b32 p.batch)]) :
    countedUntil 2768 vs ≤ mmaTripsBudget + 2 * groupsBudget p + 1194 := by
  have hb := boundSilent (P := fun _ => True) 8 (by decide) hw hs.1
    (atShape hs) trivial (fun _ _ _ _ => trivial)
    (budget := mmaTripsBudget + 2 * groupsBudget p + 1193) (fun hr _ _ _ _ hW =>
      firstScanBound hp hCta hW (groupInitFromRun .select hCta hs hr))
  simpa only [Nat.add_left_comm 1, Nat.reduceAdd] using hb

/-- Every finite prefix of the MMA role after reading the batch ABI word has bounded counted
work, regardless of where it stops or how many failed polls it contains. -/
theorem mmaRolePrefixBound (hs : At s 1907 [(7203, b32 p.batch), (1072, b32 cta)]) :
    countedUntil 2768 vs ≤ 256 * 2 ^ 32 + 128 * (p.batch + 1) + 1364 := by
  have hNoWrite : ((kernel.code.drop 1907).take (1985 - 1907)).all
      (fun i => !(mmaWrites i.op).contains 7203) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hKeep {v u : TState} {e : Option Event} (hl : 1907 ≤ v.pc) (hh : v.pc < 1985)
      (he : WStep kernel Assumptions.all l g v e u)
      (h : ctaReg cta v ∧ batchReg 7203 p.batch v) :
      ctaReg cta u ∧ batchReg 7203 p.batch u :=
    ⟨preserveCta 0 hl hh he h.1, preserveBatch (by decide) hNoWrite hl hh he h.2⟩
  have hPrefix := phaseLinearBound (hi := 1985) (budget := 170) 0 hw
    (by rw [hs.1]; decide) (by decide) (atShape hs) (by decide)
  have hb := boundRegion 0 hw hs.1.ge (by rw [hs.1]; decide) (atShape hs)
    (show ctaReg cta s ∧ batchReg 7203 p.batch s from ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.1⟩)
    hKeep hPrefix (m := mmaTripsBudget + 2 * groupsBudget p + 1194) (by
      intro u rest tail he hf hu ⟨hCTA, hBatch⟩ hW
      have hE : u.pc = 1985 ∨ u.pc = 2042 := by simpa [roleRegion] using he
      rcases hE with ha | hb
      · exact firstSetupBound hp hCta hW (shapeAt ha hu hf (by decide) ⟨hCTA, hBatch, trivial⟩)
      · exact (selectedBound hp hCta hW hb hu hCTA).trans (by omega))
  simpa only [Nat.add_left_comm 170, Nat.reduceAdd, groupsBudget, ← Nat.mul_assoc,
    Nat.reduceMul, mmaTripsBudget_eq] using hb
end

end
end
end PTX.Kernels.TmlFa4Fwd.Mma
