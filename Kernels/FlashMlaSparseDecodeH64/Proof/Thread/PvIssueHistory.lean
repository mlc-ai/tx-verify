-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmReuseEndpoints
import Lemmas.Flow.Final

public section

/-! # The eight PV issues tracked by a commit and their observed value bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PvIssueHistory

open PTX PTX.Flow

private def phase : Wg1Mma.Site → Option Nat
  | .pvMma k => some k.val
  | .pvCommit => some 8
  | _ => none

variable {P : Params} {L : Launch}

set_option maxHeartbeats 1200000 in
private theorem role_predecessor {g n : Nat} {q d : Wg1Mma.D} {e : Event}
    (hn : Wg1Mma.next P L g q e = some (some d)) (hd : phase d.site = some (n + 1))
    : phase q.site = some n ∧ q.i = d.i := by
  cases hq : q.site <;> simp only [Wg1Mma.next, hq, Wg1Mma.nextSite] at hn
  case pvMma k =>
    have hk := k.isLt
    split at hn <;> cases hn
    all_goals simp only [phase, Option.some.injEq] at hd ⊢
    all_goals exact ⟨by omega, trivial⟩
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp only [hq, Wg1Mma.startSite, Wg1Mma.afterTopk] at hd
  all_goals try split_ifs at hd
  all_goals simp [phase] at hd

private theorem machine_predecessor {g n : Nat} {s : Machine.ThreadD} {d : Wg1Mma.D} {e : Event}
    (hn : Machine.next P L g s e = some (some (.mma d))) (hd : phase d.site = some (n + 1)) :
    ∃ q, s = .mma q ∧ phase q.site = some n ∧ q.i = d.i := by
  cases s
  case mma q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i q' hnext
      cases hn
      exact ⟨q, rfl, role_predecessor hnext hd⟩
    · split at hn <;> cases hn
    · split at hn <;> cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn
    all_goals cases hn
    simp [phase] at hd
  case prologue st =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
        · cases hn
      · cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem prior_phase {X : Execution} {g j n : Nat} {k : Fin 8} {d : Wg1Mma.D}
    (hbound : j ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hphase : phase d.site = some (k.val + n)) :
    ∃ i q, i + n = j ∧ q.site = .pvMma k ∧ q.i = d.i ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) := by
  induction n generalizing j d with
  | zero =>
    have hsite : d.site = .pvMma k := by
      cases hd : d.site <;> simp [phase, hd] at hphase
      · exact congrArg Wg1Mma.Site.pvMma (Fin.ext hphase)
      · have := k.isLt
        omega
    exact ⟨j, d, rfl, hsite, rfl, hs⟩
  | succ n ih =>
    cases j with
    | zero => rw [Frame.stateAt_zero] at hs; cases hs
    | succ j =>
      have hj : j < (X.tr g).length := by omega
      have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
      rw [Frame.stateAt_succ (C := Machine.code P L) he] at hs
      cases hp : Frame.stateAt (Machine.code P L) X g j with
      | none => simp [hp] at hs
      | some σ =>
        cases σ with
        | none => simp [hp] at hs; cases hs
        | some s =>
          rw [hp, Option.bind_some] at hs
          obtain ⟨q, rfl, hq, hb⟩ := machine_predecessor hs hphase
          obtain ⟨i, t, hi, ht, hiBlock, hstate⟩ := ih hj.le hp hq
          exact ⟨i, t, by omega, ht, hiBlock.trans hb, hstate⟩

/-- The state for any of the eight PV issues before an actual commit of their block. -/
theorem pv_state_of_commit {X : Execution} {g j : Nat} {d : Wg1Mma.D} {e : Event}
    (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d))) (hc : d.site = .pvCommit)
    (k : Fin 8) :
    ∃ i, i + (8 - k.val) = j ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, d.i⟩)) := by
  have hk := k.isLt
  have hphase : phase d.site = some (k.val + (8 - k.val)) := by
    simp only [hc, phase, Option.some.injEq]
    omega
  obtain ⟨i, ⟨site, block⟩, hi, rfl, rfl, hstate⟩ :=
    prior_phase (PTX.len_of_get he).le hd hphase
  exact ⟨i, hi, hstate⟩

private theorem issue_of_earlier_state {mem0 : Mem0} {X : Execution} {g i j block : Nat} {k : Fin 8}
    {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, j) = some e) (hij : i < j)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩))) :
    X.MmaIssue (g, i) (Wg1Mma.pvDest k) (MmaDataTrace.pvOperands L g block k)
      (MmaDataTrace.pvAccum block k) [0, 0, 0, 0] := by
  have hj := PTX.len_of_get he
  change j < (X.tr g).length at hj
  have hiLen : i < (X.tr g).length := by omega
  let ev := (X.tr g)[i]
  have hget : X.get (g, i) = some ev := List.getElem?_eq_getElem hiLen
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, u, ha, _, hcode, hf⟩ := Frame.fired_site hs hX hget hi
  cases u with
  | none =>
    obtain ⟨_, hrun⟩ := hX.thr g hg
    have := PTX.Flow.Run.end_last hrun hget (fires_none_ends hf)
    omega
  | some u =>
    have hk := (MmaDataTrace.fires_pvMma hpre hg block k ha hcode hf).1
    obtain ⟨site, kind⟩ := ev
    change kind = _ at hk
    exact ⟨site, by rw [hget, hk]⟩

/-- An actual PV issue fixes every earlier issue of the same block by index. -/
theorem pv_issue_before {mem0 : Mem0} {X : Execution} {g j block : Nat} {e : Event} {last : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma ⟨.pvMma last, block⟩)))
    (k : Fin 8) (hk : k.val < last.val) :
    ∃ i, i + (last.val - k.val) = j ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩)) ∧
      X.MmaIssue (g, i) (Wg1Mma.pvDest k) (MmaDataTrace.pvOperands L g block k)
        (MmaDataTrace.pvAccum block k) [0, 0, 0, 0] := by
  have hPhase : phase (.pvMma last) = some (k.val + (last.val - k.val)) := by
    simp only [phase, Option.some.injEq]
    omega
  obtain ⟨i, ⟨site, block'⟩, hi, hSite, hBlock, hState⟩ :=
    prior_phase (PTX.len_of_get he).le hd hPhase
  change site = _ at hSite
  change block' = block at hBlock
  subst site block'
  exact ⟨i, hi, hState, issue_of_earlier_state hpre hX hs he (by omega) hState⟩

/-- The indexed PV event before an actual commit issued that block's matching operands. -/
theorem pv_issue_of_commit {mem0 : Mem0} {X : Execution} {g j : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d))) (hc : d.site = .pvCommit)
    (k : Fin 8) :
    ∃ i, i + (8 - k.val) = j ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, d.i⟩)) ∧
      X.MmaIssue (g, i) (Wg1Mma.pvDest k) (MmaDataTrace.pvOperands L g d.i k)
        (MmaDataTrace.pvAccum d.i k) [0, 0, 0, 0] := by
  obtain ⟨i, hi, hState⟩ := pv_state_of_commit he hd hc k
  have := k.isLt
  exact ⟨i, hi, hState, issue_of_earlier_state hpre hX hs he (by omega) hState⟩

/-- A completed PV issue supplies an actual observation of each byte in its B operand. -/
theorem pv_operand_byte_observed {X : Execution} {L : Launch} {g i block dest index : Nat}
    {issue : Fin 8} {accum : Bool} {mask : List Nat} {l : Loc}
    (heffects : AsyncCopy.TcEffectsOk X) (hdone : X.AsyncPresent (g, i) .mmaDone)
    (hissue : X.MmaIssue (g, i) dest (MmaDataTrace.pvOperands L g block issue) accum mask)
    (hindex : index < TcMma.Operand.b.bytes Wg1Mma.pvDescriptor)
    (hfoot : X.MmaFootprint (g, i) true index l) :
    ∃ value, X.MmaRead (g, i) true index l value := by
  have hread := heffects.1 (g, i) (heffects.2 (g, i) hdone)
  obtain ⟨site, hget⟩ := hissue
  rcases hread with ⟨d, s, acc, m, operands, ⟨tag, he⟩, hobs, hvalid, ha, hb⟩ |
      ⟨c, operands, ⟨tag, he⟩, _⟩ | ⟨s, operands, ⟨tag, he⟩, _⟩
  · rw [hget] at he
    cases he
    have hlen : index < operands.b.length := by rw [hb]; exact hindex
    exact ⟨operands.b[index], hfoot, operands, hobs, List.getElem?_eq_getElem hlen⟩
  · rw [hget] at he
    cases he
  · rw [hget] at he
    cases he

/-- A dequantization lane's store offset agrees with the SW128 byte offset of the PV operand. -/
theorem pv_dequant_offset {L : Launch} {writer : Nat} {lane : Fin 128}
    (htid : tidOf L writer = 256 + lane.val) (r : Fin 4) (s : Fin 8) (b : Fin 16) :
    MmaDataTrace.pvDequantByteOffset lane r s b = Wg2.tileOff L writer r.val s.val + b.val := by
  have hl := lane.isLt
  have hgroup : Wg2.groupIdx L writer = lane.val / 8 := by
    simp only [Wg2.groupIdx, Wg2.idxInWg, Wg2.groupSize, htid]
    omega
  have hidx : Wg2.idxInGroup L writer = lane.val % 8 := by
    simp only [Wg2.idxInGroup, Wg2.groupSize, htid]
    omega
  simp only [MmaDataTrace.pvDequantByteOffset, Wg2.tileOff, Wg2.dstOff, Wg2.rowInAtom,
    hgroup, hidx, Wg2.numGroups, Wg2.topkBlock]
  omega

/-- A completed PV issue observes the corresponding byte of an actual dequantization lane's
shared store footprint, with the block selecting the ring slot. -/
theorem dequant_operand_byte_observed {mem0 : Mem0} {X : Execution} {g i block dest writer : Nat}
    {accum : Bool} {mask : List Nat} {lane : Fin 128} (hpre : Pre P L mem0)
    (heffects : AsyncCopy.TcEffectsOk X) (hcta : ctaOf L g = ctaOf L writer)
    (htid : tidOf L writer = 256 + lane.val) (r : Fin 4) (s : Fin 8) (b : Fin 16)
    (hdone : X.AsyncPresent (g, i) .mmaDone)
    (hissue : X.MmaIssue (g, i) dest
      (MmaDataTrace.pvOperands L g block (MmaDataTrace.pvDequantIssue r s)) accum mask) :
    ∃ value, X.MmaRead (g, i) true (MmaDataTrace.pvDequantIndex lane s b)
      ⟨.shared, ctaOf L writer,
        L.sharedBase + Wg2.tileBase (block % 2) + Wg2.tileOff L writer r.val s.val + b.val⟩
        value := by
  have hloc := MmaDataTrace.pvDequantByteLoc (g := g) hpre block lane r s b
  rw [hcta, pv_dequant_offset htid] at hloc
  have hfoot : X.MmaFootprint (g, i) true (MmaDataTrace.pvDequantIndex lane s b)
      ⟨.shared, ctaOf L writer,
        L.sharedBase + Wg2.tileBase (block % 2) + Wg2.tileOff L writer r.val s.val + b.val⟩ :=
    .inl ⟨_, _, _, _, hissue, by
      simpa only [ite_true, Wg1Mma.kvBase, Wg2.tileBase, Wg2.dequantBytes, Nat.add_assoc]
        using hloc⟩
  exact pv_operand_byte_observed heffects hdone hissue
    (MmaDataTrace.pvDequantIndex_lt lane s b) hfoot

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PvIssueHistory
