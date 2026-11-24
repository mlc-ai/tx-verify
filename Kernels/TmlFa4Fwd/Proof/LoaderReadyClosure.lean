-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyHistory
public import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MmaRingAddress
public import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
public import Kernels.TmlFa4Fwd.Proof.OutputBarrierFacts
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal
public import Lemmas.Flow.NotCommit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow Prologue

noncomputable section

private def loaderArrivals : List Nat := [686, 711, 737, 763, 1153, 1182, 1368, 1900]
private def epilogueArrivals : List Nat := [2983, 2985]
private def softmaxArrivals : List Nat := [3590, 4847, 4867, 5278, 6532, 6552, 7437, 7457]
private def correctionArrivals : List Nat :=
  [7752, 7754, 7987, 8223, 8224, 8442, 8443, 8464, 8468, 8759, 8760, 8764, 9055, 9056]

private theorem arriveSites :
    OpPcsFast kernel.code arriveOp
      (loaderArrivals ++ epilogueArrivals ++ softmaxArrivals ++ correctionArrivals) = true := by
  decide +kernel

private theorem inArriveSites {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc : Nat} {loc : Loc}
    {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩) :
    pc ∈ loaderArrivals ∨ pc ∈ epilogueArrivals ∨ pc ∈ softmaxArrivals ∨
      pc ∈ correctionArrivals := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hBad
  obtain ⟨_, _, _, _, _, _, _, hOp, _⟩ := fires_arrive_flags hf rfl
  have hSite := OpPcsFast.mem arriveSites hc (show arriveOp ins.op = true by rw [hOp]; rfl)
  simpa only [List.mem_append, or_assoc] using hSite

/-- Shared offsets used by the actual ordinary arrivals. -/
def ordinaryArriveOffsets : List Nat :=
  [0, 8, 320, 328, 224, 232, 96, 104, 112, 120, 336, 344, 192, 200, 208, 216]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Resolve every ordinary barrier arrival to one of the frozen offsets. -/
theorem actualArriveOffsetIn {i : EvId} {pc : Nat} {loc : Loc} {tx count : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩) :
    ∃ off ∈ ordinaryArriveOffsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩ := by
  have widen {offsets : List Nat} (hTab : offsets.all ordinaryArriveOffsets.contains = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) :
      ∃ off ∈ ordinaryArriveOffsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩ := by
    obtain ⟨off, hm, hLoc⟩ := h
    exact ⟨off, List.contains_iff_mem.mp (List.all_eq_true.mp hTab off hm), hLoc⟩
  rcases inArriveSites hX he with h | h | h | h
  · exact widen (by decide) (Loader.loaderFixedArriveAddress hp hX he h)
  · exact widen (by decide) (OutputWarp.arriveAddress hp hX he
      (by simpa [epilogueArrivals] using h))
  · exact widen (by decide) (Softmax.softmaxArriveAddress hp hX he h)
  · exact widen (by decide) (Correction.correctionArriveAddress hp hX he h)

/-- The actual ordinary arrivals target initialized objects outside the KV-ready ring. -/
theorem actualArriveOffset {i : EvId} {pc : Nat} {loc : Loc} {tx count : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩) :
    ∃ off, initializedMbarOffset off ∧ (off < 32 ∨ 48 < off) ∧
      loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩ := by
  obtain ⟨off, hm, hLoc⟩ := actualArriveOffsetIn hp hX he
  have hTab : ordinaryArriveOffsets.all (fun a =>
      decide (a % 8 = 0 ∧ (a ≤ 232 ∨ 320 ≤ a ∧ a ≤ 344) ∧
        (a < 32 ∨ 48 < a))) = true := by decide
  obtain ⟨ha, hr, hOutside⟩ := of_decide_eq_true (List.all_eq_true.mp hTab off hm)
  exact ⟨off, ⟨ha, hr⟩, hOutside, hLoc⟩

/-- The two credits acquired before the first Q issue receive no ordinary release arrival. -/
theorem noOrdinaryInitialInputCredit {i : EvId} {cta offset tx count : Nat} {release : Bool}
    {scope : MbarScope} (hOffset : offset = 16 ∨ offset = 56) :
    ¬ X.Arrive i ⟨.shared, cta, l.sharedBase + offset⟩ tx count release scope := by
  rintro ⟨_, he⟩
  obtain ⟨off, hIn, hLoc⟩ := actualArriveOffsetIn hp hX he
  have hEq := Nat.add_left_cancel (congrArg Loc.addr hLoc)
  subst off
  rcases hOffset with rfl | rfl <;> exact (by decide : _ ∉ ordinaryArriveOffsets) hIn

/-- Ordinary arrivals on the two query barriers are loader expect-transaction instructions. -/
theorem actualQueryCreditSite (stage : Fin 2) {i : EvId} {pc : Nat} {loc : Loc} {tx count : Nat}
    {rel : Bool} {scope : MbarScope} (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩)
    (hAddr : loc.addr = l.sharedBase + 8 * stage.val) :
    pc ∈ (if stage.val = 0 then [686] else [737, 1900]) := by
  have outside {offsets : List Nat} (hAudit : offsets.all (fun off =>
      decide (off ≠ 8 * stage.val)) = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, hm, hLoc⟩ := h
    have hA : loc.addr = l.sharedBase + off := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit off hm)) (by omega)
  rcases inArriveSites hX he with h | h | h | h
  · obtain ⟨g, index⟩ := i
    have hLoc := Loader.loaderFixedArriveOffset hp hX he h
    have hEq : l.sharedBase + 8 * stage.val = l.sharedBase + Loader.loaderExpectTxOffset pc :=
      hAddr.symm.trans (congrArg Loc.addr hLoc)
    let sources := if stage.val = 0 then [686] else [737, 1900]
    have hAudit : loaderArrivals.all (fun pc =>
        decide (Loader.loaderExpectTxOffset pc = 8 * stage.val → pc ∈ sources)) = true := by
      fin_cases stage <;> decide
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit pc h)) (by omega)
  · exact (outside (by fin_cases stage <;> decide)
      (OutputWarp.arriveAddress hp hX he (by simpa [epilogueArrivals] using h))).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Softmax.softmaxArriveAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Correction.correctionArriveAddress hp hX he h)).elim

/-- Ordinary arrivals on the two Bias-ready barriers are loader expect-transaction instructions. -/
theorem actualBiasCreditSite (stage : Fin 2) {i : EvId} {pc : Nat} {loc : Loc} {tx count : Nat}
    {rel : Bool} {scope : MbarScope} (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩)
    (hAddr : loc.addr = l.sharedBase + (320 + 8 * stage.val)) :
    pc ∈ (if stage.val = 0 then [711, 1153, 1368] else [763, 1182]) := by
  have outside {offsets : List Nat} (hAudit : offsets.all (fun off =>
      decide (off ≠ (320 + 8 * stage.val))) = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, hm, hLoc⟩ := h
    have hA : loc.addr = l.sharedBase + off := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit off hm)) (by omega)
  rcases inArriveSites hX he with h | h | h | h
  · obtain ⟨g, index⟩ := i
    have hLoc := Loader.loaderFixedArriveOffset hp hX he h
    have hEq := hAddr.symm.trans (congrArg Loc.addr hLoc)
    change l.sharedBase + (320 + 8 * stage.val) =
      l.sharedBase + Loader.loaderExpectTxOffset pc at hEq
    let sources := if stage.val = 0 then [711, 1153, 1368] else [763, 1182]
    have hAudit : loaderArrivals.all (fun pc =>
        decide (Loader.loaderExpectTxOffset pc = (320 + 8 * stage.val) → pc ∈ sources)) = true := by
      fin_cases stage <;> decide
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit pc h)) (by omega)
  · exact (outside (by fin_cases stage <;> decide)
      (OutputWarp.arriveAddress hp hX he (by simpa [epilogueArrivals] using h))).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Softmax.softmaxArriveAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Correction.correctionArriveAddress hp hX he h)).elim

/-- The Bias return objects receive the softmax release of a Bias buffer. -/
theorem actualBiasEmptyArrivalSite (stage : Fin 2) {i : EvId} {pc : Nat} {loc : Loc}
    {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩)
    (hAddr : loc.addr = l.sharedBase + (336 + 8 * stage.val)) :
    pc ∈ [3590, 5278] := by
  have outside {offsets : List Nat} (hAudit : offsets.all (fun off =>
      decide (off ≠ 336 + 8 * stage.val)) = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, hm, hLoc⟩ := h
    have hA : loc.addr = l.sharedBase + off := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit off hm)) (by omega)
  rcases inArriveSites hX he with h | h | h | h
  · exact (outside (by fin_cases stage <;> decide)
      (Loader.loaderFixedArriveAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> decide)
      (OutputWarp.arriveAddress hp hX he (by simpa [epilogueArrivals] using h))).elim
  · by_contra hSite
    have hShape := Softmax.softmaxArriveAddressClass hp hX he h
    rw [ite_eq_right hSite] at hShape
    exact outside (by fin_cases stage <;> decide) hShape
  · exact (outside (by fin_cases stage <;> decide)
      (Correction.correctionArriveAddress hp hX he h)).elim

/-- A probability barrier's ordinary updates come from softmax publication or correction. -/
theorem actualProbabilityArrivalSite {i : EvId} {pc : Nat} {loc : Loc} {tx count : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩) {offset : Nat}
    (hOffset : offset ∈ [96, 104, 112, 120]) (hAddr : loc.addr = l.sharedBase + offset) :
    (∃ site : Fin 6, pc = (Softmax.probabilityArrivalSite site).pc) ∨
      pc ∈ [7752, 7754, 8223, 8442, 8759, 9055] := by
  have outside {offsets : List Nat}
      (hAudit : offsets.all (fun off => !([96, 104, 112, 120] : List Nat).contains off) = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, hm, hLoc⟩ := h
    have hA : loc.addr = l.sharedBase + off := congrArg Loc.addr hLoc
    have heq : off = offset := by omega
    have hNo := List.all_eq_true.mp hAudit off hm
    rw [heq, List.contains_iff_mem.mpr hOffset] at hNo
    cases hNo
  rcases inArriveSites hX he with h | h | h | h
  · exact (outside (by decide) (Loader.loaderFixedArriveAddress hp hX he h)).elim
  · exact (outside (by decide) (OutputWarp.arriveAddress hp hX he
      (by simpa [epilogueArrivals] using h))).elim
  · left
    have hBias : pc ∉ [3590, 5278] := by
      intro hm
      have hCase := Softmax.softmaxArriveAddressClass hp hX he h
      rw [ite_eq_left hm] at hCase
      exact outside (by decide) hCase
    have hClasses : ∀ q ∈ softmaxArrivals, q ∉ [3590, 5278] →
        ∃ site : Fin 6, q = (Softmax.probabilityArrivalSite site).pc := by decide
    exact hClasses pc h hBias
  · right
    obtain ⟨g, index⟩ := i
    have hActual := Correction.correctionArriveAddressExact hp hX he h
    have hA : loc.addr = l.sharedBase + Correction.correctionArriveOffset pc :=
      congrArg Loc.addr hActual
    have hEq : offset = Correction.correctionArriveOffset pc := by omega
    have hClasses : ∀ q ∈ correctionArrivals,
        Correction.correctionArriveOffset q ∈ [96, 104, 112, 120] →
          q ∈ [7752, 7754, 8223, 8442, 8759, 9055] := by decide
    exact hClasses pc h (hEq ▸ hOffset)

omit hp hX in
/-- Tensor Core commit sites with a fixed barrier operand. -/
def fixedCommits : List Nat := [2208, 2270, 2274, 2418, 2519, 2537, 2541, 2642, 2646]
omit hp hX in
/-- Tensor Core commit sites with a rotating barrier operand. -/
def ringCommits : List Nat := [2462, 2523, 2638]

omit hp hX in
private theorem commitSites :
    OpPcsFast kernel.code commitOp (fixedCommits ++ ringCommits) = true := by
  decide +kernel

omit hp hX in
/-- Every actual commit belongs to one of the two audited address classes. -/
theorem inCommitSites {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc : Nat} {s : TcCommit.Spec}
    (he : X.get i = some ⟨pc, .tc (.commit s)⟩) : pc ∈ fixedCommits ∨ pc ∈ ringCommits := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hBad
  have hCommit : commitOp ins.op = true := by
    cases h : commitOp ins.op
    · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) hf s rfl).elim
    · rfl
  simpa only [List.mem_append] using OpPcsFast.mem commitSites hc hCommit

theorem actualCommitOffsetIn {i : EvId} {pc : Nat} {s : TcCommit.Spec} {rank : Fin 16}
    {target : Loc} (he : X.get i = some ⟨pc, .tc (.commit s)⟩)
    (hTarget : TcCommit.target s rank = some target) :
    ∃ off ∈ [16, 24, 56, 64, 72, 80, 88, 144, 152],
      target = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩ := by
  rcases inCommitSites hX he with h | h
  · obtain ⟨off, ho, hl⟩ := Mma.mmaFixedCommitAddress hp hX he h hTarget
    have hAudit : [16, 24, 56, 80, 88, 144, 152].all
        (fun n => [16, 24, 56, 64, 72, 80, 88, 144, 152].contains n) = true := by decide
    have hm : off ∈ [16, 24, 56, 80, 88, 144, 152] := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false,or_left_comm,or_comm,or_assoc] using ho
    exact ⟨off, List.contains_iff_mem.mp (List.all_eq_true.mp hAudit off hm), hl⟩
  · obtain ⟨slot, hl⟩ := Mma.mmaRingCommitAddress hp hX he h hTarget
    exact ⟨8 * slot.val + 56,
      (by decide : ∀ j : Fin 3, 8 * j.val + 56 ∈ [16,24,56,64,72,80,88,144,152]) slot,hl⟩

/-- The actual MMA commit targets are initialized objects outside the KV-ready ring. -/
theorem actualCommitOffset {i : EvId} {pc : Nat} {s : TcCommit.Spec} {rank : Fin 16} {target : Loc}
    (he : X.get i = some ⟨pc, .tc (.commit s)⟩) (hTarget : TcCommit.target s rank = some target) :
    ∃ off, initializedMbarOffset off ∧ (off < 32 ∨ 48 < off) ∧
      target = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩ := by
  obtain ⟨off, hOff, hLoc⟩ := actualCommitOffsetIn hp hX he hTarget
  have hAudit : [16, 24, 56, 64, 72, 80, 88, 144, 152].all
      (fun n => decide ((n % 8 = 0 ∧ (n ≤ 232 ∨ 320 ≤ n ∧ n ≤ 344)) ∧
        (n < 32 ∨ 48 < n))) = true := by decide
  obtain ⟨hInitialized, hOutside⟩ := of_decide_eq_true (List.all_eq_true.mp hAudit off hOff)
  exact ⟨off, hInitialized, hOutside, hLoc⟩

/-- An ordinary arrival targeting an output-free object comes from the epilogue. -/
theorem actualOutputFreeArrivalSite {i : EvId} {pc : Nat} {loc : Loc} {tx count : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩)
    (hAddr : loc.addr = l.sharedBase + 224 ∨ loc.addr = l.sharedBase + 232) :
    pc = 2983 ∨ pc = 2985 := by
  have outside {offsets : List Nat}
      (hAudit : offsets.all (fun off => decide (off ≠ 224 ∧ off ≠ 232)) = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, hOff, hLoc⟩ := h
    obtain ⟨h₀, h₁⟩ := of_decide_eq_true (List.all_eq_true.mp hAudit off hOff)
    have hEq := congrArg Loc.addr hLoc
    rcases hAddr with h | h
    · exact h₀ (by simp only [h] at hEq; omega)
    · exact h₁ (by simp only [h] at hEq; omega)
  rcases inArriveSites hX he with h | h | h | h
  · exact (outside (by decide) (Loader.loaderFixedArriveAddress hp hX he h)).elim
  · simpa only [epilogueArrivals, List.mem_cons, List.not_mem_nil, or_false] using h
  · exact (outside (by decide) (Softmax.softmaxArriveAddress hp hX he h)).elim
  · exact (outside (by decide) (Correction.correctionArriveAddress hp hX he h)).elim

/-- The only ordinary arrivals to the statistics-buffer credit counters are the decoded
correction publications for the corresponding stage. -/
theorem actualStatsCreditArrivalSite (stage : Fin 2) {i : EvId} {pc : Nat} {loc : Loc}
    {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩)
    (hAddr : loc.addr = l.sharedBase + (192 + 8 * stage.val)) :
    pc ∈ (if stage.val = 0 then [7987, 8443, 8468] else [8224, 8464, 8764]) := by
  have outside {offsets : List Nat} (hAudit : offsets.all (fun off =>
      decide (off ≠ 192 + 8 * stage.val)) = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, hm, hLoc⟩ := h
    have hA : loc.addr = l.sharedBase + off := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit off hm)) (by omega)
  rcases inArriveSites hX he with h | h | h | h
  · exact (outside (by fin_cases stage <;> decide)
      (Loader.loaderFixedArriveAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> decide)
      (OutputWarp.arriveAddress hp hX he (by simpa [epilogueArrivals] using h))).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Softmax.softmaxArriveAddress hp hX he h)).elim
  · obtain ⟨g, j⟩ := i
    have hLoc := Correction.correctionArriveAddressExact hp hX he h
    have hA := congrArg Loc.addr hLoc
    change loc.addr = l.sharedBase + Correction.correctionArriveOffset pc at hA
    let credits := if stage.val = 0 then [7987, 8443, 8468] else [8224, 8464, 8764]
    have hAudit : correctionArrivals.all (fun pc => decide
        (Correction.correctionArriveOffset pc = 192 + 8 * stage.val → pc ∈ credits)) = true := by
      fin_cases stage <;> decide
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit pc h)) (by omega)

/-- Only the matching correction stage publishes to an output-ready object. -/
theorem actualOutputReadyArrivalSite (stage : Fin 2) {i : EvId} {pc : Nat} {loc : Loc}
    {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .arrive loc tx count rel scope⟩)
    (hAddr : loc.addr = l.sharedBase + (208 + 8 * stage.val)) :
    pc = Correction.outputFencePc stage + 2 := by
  have outside {offsets : List Nat} (hAudit : offsets.all (fun off =>
      decide (off ≠ 208 + 8 * stage.val)) = true)
      (h : ∃ off ∈ offsets, loc = ⟨.shared, i.1 / l.block, l.sharedBase + off⟩) : False := by
    obtain ⟨off, hm, hLoc⟩ := h
    have hA : loc.addr = l.sharedBase + off := congrArg Loc.addr hLoc
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit off hm)) (by omega)
  rcases inArriveSites hX he with h | h | h | h
  · exact (outside (by fin_cases stage <;> decide)
      (Loader.loaderFixedArriveAddress hp hX he h)).elim
  · exact (outside (by fin_cases stage <;> decide)
      (OutputWarp.arriveAddress hp hX he (by simpa [epilogueArrivals] using h))).elim
  · exact (outside (by fin_cases stage <;> decide)
      (Softmax.softmaxArriveAddress hp hX he h)).elim
  · obtain ⟨g, j⟩ := i
    have hLoc := Correction.correctionArriveAddressExact hp hX he h
    have hA := congrArg Loc.addr hLoc
    change loc.addr = l.sharedBase + Correction.correctionArriveOffset pc at hA
    have hAudit : correctionArrivals.all (fun pc => decide
        (Correction.correctionArriveOffset pc = 208 + 8 * stage.val →
          pc = Correction.outputFencePc stage + 2)) = true := by
      fin_cases stage <;> decide
    exact (of_decide_eq_true (List.all_eq_true.mp hAudit pc h)) (by omega)

/-- A Tensor Core commit cannot target a statistics-buffer credit counter. -/
theorem commitExcludesStatsCredit (stage : Fin 2) {i : EvId} {pc : Nat} {s : TcCommit.Spec}
    {rank : Fin 16} {target : Loc} (he : X.get i = some ⟨pc, .tc (.commit s)⟩)
    (hTarget : TcCommit.target s rank = some target) :
    target.addr ≠ l.sharedBase + (192 + 8 * stage.val) := by
  intro hAddr
  rcases inCommitSites hX he with h | h
  · obtain ⟨off, ho, hl⟩ := Mma.mmaFixedCommitAddress hp hX he h hTarget
    have hOff : target.addr = l.sharedBase + off := congrArg Loc.addr hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    fin_cases stage <;> simp at hAddr <;> omega
  · obtain ⟨slot, hl⟩ := Mma.mmaRingCommitAddress hp hX he h hTarget
    fin_cases slot <;> fin_cases stage <;> rw [hl] at hAddr <;>
      simp_all

/-- A Tensor Core commit cannot target an output-ready object. -/
theorem commitExcludesOutputReady (stage : Fin 2) {i : EvId} {pc : Nat} {s : TcCommit.Spec}
    {rank : Fin 16} {target : Loc} (he : X.get i = some ⟨pc, .tc (.commit s)⟩)
    (hTarget : TcCommit.target s rank = some target) :
    target.addr ≠ l.sharedBase + (208 + 8 * stage.val) := by
  intro hAddr
  rcases inCommitSites hX he with h | h
  · obtain ⟨off, ho, hl⟩ := Mma.mmaFixedCommitAddress hp hX he h hTarget
    have hOff : target.addr = l.sharedBase + off := congrArg Loc.addr hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    fin_cases stage <;> simp at hAddr <;> omega
  · obtain ⟨slot, hl⟩ := Mma.mmaRingCommitAddress hp hX he h hTarget
    fin_cases slot <;> fin_cases stage <;> rw [hl] at hAddr <;>
      simp_all
end

namespace Loader

private theorem outsideReadySlot {l : Launch} {cta own off : Nat} (stage : Fin 3)
    (hOutside : off < 32 ∨ 48 < off) :
    (⟨.shared, own, l.sharedBase + off⟩ : Loc) ≠ initObject l cta (readySlot stage) := by
  intro h
  rw [readySlot_address] at h
  have ha := congrArg Loc.addr h
  change l.sharedBase + off = l.sharedBase + 8 * stage.val + 32 at ha
  have := stage.isLt
  omega

private theorem readyTargetExclusions {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (cta : Nat) (stage : Fin 3) :
    let loc := initObject l cta (readySlot stage)
    (∀ i tx count release scope, ¬ X.Arrive i loc tx count release scope) ∧
      (∀ i addr spec, X.TensorIssue i addr spec → spec.mbar ≠ loc) ∧
      (∀ i spec rank, X.Commit i spec → TcCommit.target spec rank ≠ some loc) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rintro i tx count release scope ⟨pos, hGet⟩
    obtain ⟨off, _, hOutside, hl⟩ := actualArriveOffset hp hX hGet
    exact outsideReadySlot stage hOutside hl.symm
  · rintro i addr s ⟨pos, hGet⟩ hBad
    obtain ⟨j, rfl⟩ := actualInputIssuePc hX hGet
    obtain ⟨off, hm, hl⟩ := loaderTensorAddress hp hX j hGet
    have hOutside : off < 32 ∨ 48 < off := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    exact outsideReadySlot stage hOutside (hl.symm.trans hBad)
  · rintro i s rank ⟨pos, hGet⟩ hTarget
    obtain ⟨off, _, hOutside, hl⟩ := actualCommitOffset hp hX hGet hTarget
    exact outsideReadySlot stage hOutside hl.symm

/-- The ready object is initialized and only receives no-increment arrivals
as soon as its history contains any actual record. -/
theorem actualReadyHistoryObject {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 3) {r : MBarrier.Record AsyncCopy.Ref}
    (hMem : r ∈ X.objects (initObject l cta (readySlot stage))) :
    PTX.MbarRing.NoIncObject X (initObject l cta (readySlot stage)) 64 := by
  obtain ⟨ha, ht, hc⟩ := readyTargetExclusions hp hX cta stage
  exact readyHistoryObject hp hX stage hMem ha ht hc

/-- Role address closure discharges every non-copy update exclusion of the KV-ready barrier.
It recovers the actual successful history record in any consistent prefix. -/
theorem actualReadyAcquireRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta pc parity : Nat} (stage : Fin 3) {wait : EvId}
    (hWait : X.get wait = some ⟨pc,
      .wait (initObject l cta (readySlot stage)) parity true true .cta⟩) :
    let loc := initObject l cta (readySlot stage)
    PTX.MbarRing.NoIncObject X loc 64 ∧ ∃ (j : Nat) (poll : MBarrier.Record AsyncCopy.Ref),
      (X.objects loc)[j]? = some poll ∧ poll.id = .thread wait ∧ poll.reply.waited = some true := by
  obtain ⟨ha, ht, hc⟩ := readyTargetExclusions hp hX cta stage
  exact readyAcquireRecord hp hX stage hWait ha ht hc

end Loader
end
end PTX.Kernels.TmlFa4Fwd
