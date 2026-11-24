-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
public import Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

private def loaderWaits : List Nat :=
  [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893, 960, 1206, 1430, 1611, 1866, 1877, 1888]

private def mmaWaits : List Nat := List.ofFn (fun site : Fin 14 => (Mma.waitSite site).pc)
private def epilogueWaits : List Nat := [2958, 2972]
private def softmaxWaits : List Nat := [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738]
private def correctionWaits : List Nat := [8473, 8476, 8769, 8772, 9201]

private def pollOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

private theorem pollSites :
    OpPcsFast kernel.code pollOp
      (loaderWaits ++ mmaWaits ++ epilogueWaits ++ softmaxWaits ++ correctionWaits) = true := by
  decide +kernel

private theorem inWaitSites {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc q : Nat} {target : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .wait target q ok acq scope⟩) :
    pc ∈ loaderWaits ∨ pc ∈ mmaWaits ∨ pc ∈ epilogueWaits ∨
      pc ∈ softmaxWaits ∨ pc ∈ correctionWaits := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hBad
  obtain ⟨_, _, _, _, _, ho, _⟩ := fires_wait_flags hf rfl
  have hSite := OpPcsFast.mem pollSites hc (show pollOp ins.op = true by rw [ho]; rfl)
  simpa only [List.mem_append, or_assoc] using hSite

/-- Partition actual wait sites by their loader, MMA, epilogue, softmax, or correction role. -/
theorem actualWaitRoleSites {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc q : Nat} {target : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc,.wait target q ok acq scope⟩) :
    pc ∈ ([517,679,704,730,756,782,1146,1175,1361,1893] ++
      [960,1206,1430,1611,1866,1877,1888] : List Nat) ∨
    pc ∈ List.ofFn (fun site : Fin 14 => (Mma.waitSite site).pc) ∨
    pc ∈ ([2958,2972] : List Nat) ∨
    pc ∈ ([3420,3425,3498,4874,5109,5181,6558,6676,7463,7738] : List Nat) ∨
    pc ∈ ([8473,8476,8769,8772,9201] : List Nat) :=
  inWaitSites hX he

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Every actual wait names one of the CTA's initialized mbarrier objects. -/
theorem actualWaitInitObject (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc q : Nat} {target : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .wait target q ok acq scope⟩) :
    ∃ site : Fin 34, target = initObject l (i.1 / l.block) site := by
  have hSite := inWaitSites hX he
  rcases hSite with h | h | h | h | h
  · exact Loader.loaderWaitInitObject hp hX he h
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    exact Mma.mmaWaitInitObject hp hX j he
  · exact OutputWarp.waitInitObject hp hX he (by simpa [epilogueWaits] using h)
  · exact Softmax.softmaxWaitInitObject hp hX he h
  · exact Correction.correctionWaitInitObject hp hX he h

/-- Loader waits whose object depends on the cache ring cursor. -/
def loaderCacheRingWaitSites : List Nat := [960, 1206, 1430, 1611, 1866, 1877, 1888]

/-- MMA waits whose object depends on the cache ring cursor. -/
def mmaCacheRingWaitSites : List Nat := [2294, 2352, 2545]

/-- The loader and MMA barrier polls that can select a cache ring slot. -/
def cacheRingWaitSites : List Nat := loaderCacheRingWaitSites ++ mmaCacheRingWaitSites

/-- At a fixed wait instruction, lanes of the same warp name the same object.
The cache ring waits select their object from a generation-dependent slot. -/
theorem waitObjectAgreementOrRing (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g g' i i' site parity parity' : Nat} {a b : Loc} {ok ok' acq acq' : Bool}
    {scope scope' : MbarScope} (hWarp : SameWarp l g g')
    (he : X.get (g,i) = some ⟨site, .wait a parity ok acq scope⟩)
    (hf : X.get (g',i') = some ⟨site, .wait b parity' ok' acq' scope'⟩) :
    a = b ∨ site ∈ cacheRingWaitSites := by
  have hCta : g / l.block = g' / l.block := hWarp.1.2.2
  have agree {off : Nat}
      (ha : a = ⟨.shared, g / l.block, l.sharedBase + off⟩)
      (hb : b = ⟨.shared, g' / l.block, l.sharedBase + off⟩) : a = b := by
    rw [hCta] at ha
    exact ha.trans hb.symm
  rcases inWaitSites hX he with hLoader | hMma | hOutput | hSoftmax | hCorrection
  · change site ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] ++
      [960, 1206, 1430, 1611, 1866, 1877, 1888] at hLoader
    rcases List.mem_append.mp hLoader with hFixed | hRing
    · exact .inl (agree (Loader.loaderFixedWaitOffset hp hX he hFixed)
        (Loader.loaderFixedWaitOffset hp hX hf hFixed))
    · exact .inr (List.mem_append_left mmaCacheRingWaitSites hRing)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hMma
    have hSplit : ∀ j : Fin 14, (Mma.waitSite j).pc ∈ cacheRingWaitSites ∨
        (Mma.waitSite j).pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] :=
      by decide
    rcases hSplit j with hRing | hFixed
    · exact .inr hRing
    · exact .inl (agree (Mma.mmaFixedWaitAddress hp hX he hFixed)
        (Mma.mmaFixedWaitAddress hp hX hf hFixed))
  · have hSite : site = 2958 ∨ site = 2972 := by simpa [epilogueWaits] using hOutput
    obtain ⟨s, hs, ha, _⟩ := OutputWarp.pollOperands hp hX he hSite
    obtain ⟨t, ht, hb, _⟩ := OutputWarp.pollOperands hp hX hf hSite
    have hSame : s = t := (by decide : ∀ s t : Fin 2,
      Epilogue.pollPc s = Epilogue.pollPc t → s = t) s t (hs.symm.trans ht)
    subst t
    exact .inl (agree ha hb)
  · have ha := (Softmax.softmaxWaitExactAddress hp hX he hSoftmax).2
    have hb := (Softmax.softmaxWaitExactAddress hp hX hf hSoftmax).2
    have hSame : warpIndex l g = warpIndex l g' := hWarp.2
    rw [hSame] at ha
    exact .inl (agree ha hb)
  · exact .inl (agree (Correction.correctionWaitExactAddress hp hX he hCorrection)
      (Correction.correctionWaitExactAddress hp hX hf hCorrection))

/-- Every poll of an output-ready object observes its initial parity. -/
theorem outputReadyPollParity (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {i : EvId} {site q : Nat} {target : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨site, .wait target q ok acq scope⟩)
    (hTarget : target.addr = l.sharedBase + (208 + 8 * stage.val)) : q = 0 := by
  obtain ⟨g, index⟩ := i
  have outside {offsets : List Nat}
      (audit : offsets.all (fun off => decide (off ≠ 208 + 8 * stage.val)) = true)
      (h : ∃ off ∈ offsets, target = ⟨.shared, g / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, ho, hLoc⟩ := h
    have hAddr : target.addr = l.sharedBase + off := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp audit off ho)) (by omega)
  rcases inWaitSites hX he with h | h | h | h | h
  · change site ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] ++
      [960, 1206, 1430, 1611, 1866, 1877, 1888] at h
    rcases List.mem_append.mp h with h | h
    · exact (outside (by fin_cases stage <;> decide)
        (Loader.loaderFixedWaitAddress hp hX he h)).elim
    · exact (outside (by fin_cases stage <;> decide)
        (Loader.loaderRingWaitAddress hp hX he h)).elim
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    have splitSlots : ∀ j : Fin 14,
        (Mma.waitSite j).pc ∈ [2294, 2352, 2545] ∨
        ((Mma.waitSite j).pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] ∧
          Mma.fixedMmaWaitOffset (Mma.waitSite j).pc < 208) := by
      decide
    rcases splitSlots j with hRing | ⟨hFixed, hBound⟩
    · obtain ⟨slot, hLoc⟩ := Mma.mmaRingWaitAddress hp hX he hRing
      have hAddr : target.addr = l.sharedBase + (8 * slot.val + 32) := congrArg Loc.addr hLoc
      have := slot.isLt
      omega
    · have hLoc := Mma.mmaFixedWaitAddress hp hX he hFixed
      have hAddr : target.addr = l.sharedBase + Mma.fixedMmaWaitOffset (Mma.waitSite j).pc :=
        congrArg Loc.addr hLoc
      omega
  · obtain ⟨_, _, _, hPhase, _, _⟩ := OutputWarp.pollOperands hp hX he
      (by simpa [epilogueWaits] using h)
    exact hPhase
  · exact (outside (by fin_cases stage <;> decide) (Softmax.softmaxWaitAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Correction.correctionWaitAddress hp hX he h)).elim

/-- The steady and terminal MMA polls of one stage's probability packet. -/
def probabilityWaitSites (stage packet : Fin 2) : List Nat :=
  if packet.val = 0 then (if stage.val = 0 then [2297, 2548] else [2419, 2595])
  else (if stage.val = 0 then [2335, 2586] else [2450, 2626])

/-- No other role polls a joint probability/rescale or tail-probability object. -/
theorem probabilityWaitSite (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {g i site cta q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g,i) =
      some ⟨site, .wait ⟨.shared, cta, l.sharedBase + (96 + 8 * stage.val + 16 * packet.val)⟩
        q ok acq scope⟩) :
    cta = g / l.block ∧ site ∈ probabilityWaitSites stage packet := by
  let off := 96 + 8 * stage.val + 16 * packet.val
  have outside {offsets : List Nat}
      (audit : offsets.all (fun n => decide (n ≠ off)) = true)
      (h : ∃ n ∈ offsets, (⟨.shared,cta,l.sharedBase + off⟩ : Loc) =
        ⟨.shared,g / l.block,l.sharedBase + n⟩) : False := by
    obtain ⟨n, hn, hLoc⟩ := h
    have hEq : l.sharedBase + off = l.sharedBase + n := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp audit n hn)) (by omega)
  rcases inWaitSites hX he with h | h | h | h | h
  · change site ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] ++
      [960, 1206, 1430, 1611, 1866, 1877, 1888] at h
    rcases List.mem_append.mp h with h | h
    · exact (outside (by fin_cases stage <;> fin_cases packet <;> decide)
        (Loader.loaderFixedWaitAddress hp hX he h)).elim
    · exact (outside (by fin_cases stage <;> fin_cases packet <;> decide)
        (Loader.loaderRingWaitAddress hp hX he h)).elim
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    have splitSlots : ∀ j : Fin 14,
        (Mma.waitSite j).pc ∈ [2294, 2352, 2545] ∨
        (Mma.waitSite j).pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] :=
      by decide
    rcases splitSlots j with hRing | hFixed
    · obtain ⟨slot, hLoc⟩ := Mma.mmaRingWaitAddress hp hX he hRing
      have hAddr : l.sharedBase + off = l.sharedBase + (8 * slot.val + 32) :=
        congrArg Loc.addr hLoc
      have := slot.isLt
      have hMin : 96 ≤ off := by dsimp [off]; omega
      omega
    · have hLoc := Mma.mmaFixedWaitAddress hp hX he hFixed
      have hAddr : l.sharedBase + off =
          l.sharedBase + Mma.fixedMmaWaitOffset (Mma.waitSite j).pc := congrArg Loc.addr hLoc
      have hEq := Nat.add_left_cancel hAddr
      have audit : ∀ (j : Fin 14) (stage packet : Fin 2),
          Mma.fixedMmaWaitOffset (Mma.waitSite j).pc = 96 + 8 * stage.val + 16 * packet.val →
          (Mma.waitSite j).pc ∈ probabilityWaitSites stage packet := by decide
      exact ⟨congrArg Loc.cta hLoc, audit j stage packet hEq.symm⟩
  · obtain ⟨outStage, _, hLoc, _⟩ := OutputWarp.pollOperands hp hX he
      (by simpa [epilogueWaits] using h)
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + off = l.sharedBase + (208 + 8 * outStage.val) at hAddr
    have hS := stage.isLt
    have hP := packet.isLt
    dsimp [off] at hAddr
    omega
  · exact (outside (by fin_cases stage <;> fin_cases packet <;> decide)
      (Softmax.softmaxWaitAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> fin_cases packet <;> decide)
      (Correction.correctionWaitAddress hp hX he h)).elim

/-- A statistics credit wait belongs to its CTA's corresponding softmax stage. -/
theorem statsCreditWaitStage (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g i site cta q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, i) =
      some ⟨site, .wait ⟨.shared, cta, l.sharedBase + (192 + 8 * stage.val)⟩ q ok acq scope⟩) :
    cta = g / l.block ∧ stage.val = warpIndex l g / 4 ∧
      site ∈ [3420, 4874, 6558, 7463, 7738] := by
  let off := 192 + 8 * stage.val
  have outside {offsets : List Nat}
      (audit : offsets.all (fun n => decide (n ≠ off)) = true)
      (h : ∃ n ∈ offsets, (⟨.shared, cta, l.sharedBase + off⟩ : Loc) =
        ⟨.shared, g / l.block, l.sharedBase + n⟩) : False := by
    obtain ⟨n, hn, hLoc⟩ := h
    have hEq : l.sharedBase + off = l.sharedBase + n := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp audit n hn)) (by omega)
  rcases inWaitSites hX he with h | h | h | h | h
  · change site ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] ++
      [960, 1206, 1430, 1611, 1866, 1877, 1888] at h
    rcases List.mem_append.mp h with h | h
    · exact (outside (by fin_cases stage <;> decide)
        (Loader.loaderFixedWaitAddress hp hX he h)).elim
    · exact (outside (by fin_cases stage <;> decide)
        (Loader.loaderRingWaitAddress hp hX he h)).elim
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    have hSites : ∀ j : Fin 14,
        (Mma.waitSite j).pc ∈ [2294, 2352, 2545] ∨
        ((Mma.waitSite j).pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] ∧
          ∀ stage : Fin 2, Mma.fixedMmaWaitOffset (Mma.waitSite j).pc ≠ 192 + 8 * stage.val) := by
      decide
    rcases hSites j with hRing | ⟨hFixed, hDifferent⟩
    · obtain ⟨slot, hLoc⟩ := Mma.mmaRingWaitAddress hp hX he hRing
      have hAddr : l.sharedBase + off = l.sharedBase + (8 * slot.val + 32) :=
        congrArg Loc.addr hLoc
      have := slot.isLt
      dsimp [off] at hAddr
      omega
    · exact (hDifferent stage (Nat.add_left_cancel
        (congrArg Loc.addr (Mma.mmaFixedWaitAddress hp hX he hFixed))).symm).elim
  · obtain ⟨outStage, _, hLoc, _⟩ := OutputWarp.pollOperands hp hX he
      (by simpa [epilogueWaits] using h)
    have hAddr : l.sharedBase + off = l.sharedBase + (208 + 8 * outStage.val) :=
      congrArg Loc.addr hLoc
    have hStage := stage.isLt
    dsimp [off] at hAddr
    omega
  · obtain ⟨o, hOffsets, hLoc⟩ := Softmax.softmaxWaitAddressClass hp hX he h
    have hSite : site ∈ [3420, 4874, 6558, 7463, 7738] := by
      by_contra hNo
      rw [ite_eq_right hNo] at hOffsets
      have hAdd : l.sharedBase + off = l.sharedBase + o := congrArg Loc.addr hLoc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hOffsets
      dsimp [off] at hAdd
      omega
    have hExact := Softmax.softmaxStatsCreditWaitAddress hp hX he hSite
    have hAddr : l.sharedBase + off = l.sharedBase + (192 + 8 * (warpIndex l g / 4)) :=
      congrArg Loc.addr hExact
    exact ⟨congrArg Loc.cta hExact, by dsimp [off] at hAddr; omega, hSite⟩
  · exact (outside (by fin_cases stage <;> decide)
      (Correction.correctionWaitAddress hp hX he h)).elim

/-- The decoded operand of every object use belongs to the same CTA and the initialized set,
including uses that have yet to contribute an asynchronous completion. -/
theorem actualMbarAddresses (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : EvId) (loc : Loc) (hUse : X.UsesMbar i loc) :
    ∃ site : Fin 34, loc = initObject l (i.1 / l.block) site := by
  rcases hUse with ⟨_, _, _, _, _, he⟩ | ⟨_, hCopy, hComp⟩ | ⟨noinc, pc, he⟩ |
    ⟨_, rank, ⟨_, he⟩, hTarget⟩ | ⟨_, _, _, _, _, he⟩ | hInval |
    ⟨_, _, ⟨_, he⟩, rfl⟩ | ⟨_, _, _, hClc, _, _⟩ | ⟨_, _, he⟩
  · obtain ⟨off, hOff, _, rfl⟩ := actualArriveOffset hp hX he
    exact initObjectOfOffset hOff
  · rw [(actualCopyShape hX hCopy).completion] at hComp
    cases hComp
  · obtain ⟨⟨j, hPc⟩, hN, _, _⟩ := Loader.actualAsyncArrival hX he
    subst noinc
    have hSite : pc ∈ [674, 904, 1137, 1342, 1602, 1735] := by
      rw [hPc]
      fin_cases j <;> decide
    exact Loader.loaderAsyncInitObject hp hX he hSite
  · obtain ⟨off, hOff, _, rfl⟩ := actualCommitOffset hp hX he hTarget
    exact initObjectOfOffset hOff
  · exact actualWaitInitObject hp hX he
  · exact (noMbarInval hX hInval).elim
  · obtain ⟨j, rfl⟩ := Loader.actualInputIssuePc hX he
    exact Loader.loaderTensorInitObject hp hX j he
  · exact (noClcIssue hX hClc).elim
  · obtain ⟨site, _, _, _, hLoc, _⟩ := actualInitializer hp hX (event_thread_lt hX he) he
    exact ⟨site, hLoc⟩

private theorem initOffsetBound :
    ∀ i : Fin 34, (initSite i).baseOffset + (initSite i).displacement ≤ 344 := by
  decide

/-- Every operand lies below the data buffers in the shared object area. -/
theorem actualMbarAddressBound (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {loc : Loc} (hi : X.UsesMbar i loc) : loc.addr ≤ l.sharedBase + 344 := by
  obtain ⟨site, rfl⟩ := actualMbarAddresses hp hX i loc hi
  have h := initOffsetBound site
  change l.sharedBase + (initSite site).baseOffset + (initSite site).displacement ≤ _
  omega

end
end PTX.Kernels.TmlFa4Fwd
