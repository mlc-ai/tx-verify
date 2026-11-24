-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields

@[expose] public section

/-! # The half-row mass updates in the actual softmax trace -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0MassHistory

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {g : Nat} {X : Execution}

/-- Sites at which the current block's probabilities have been added. -/
def updated : Wg0.Site → Bool
  | .pStore _ | .rescaleFence | .rescaleLoad _ | .rescaleWait _ | .rescaleStore _
  | .rescaleWaitSt _ | .rescaleFenceB | .soFence | .soReady | .lseBar | .lseStore0
  | .lseBar2 | .lseRead | .lseStore | .svDone | .fenceEpilogue | .oLoad _ | .oWait _
  | .oStage _ _ | .stageFence _ | .epiBar _ | .elect _ | .tmaStore _ | .commit
  | .everyone | .exit => true
  | _ => false

/-- The number of blocks already incorporated into `lh`. -/
def blocksAdded (d : D) : Nat := d.block + if updated d.site then 1 else 0

/-- Before any block is added the effective half sum is zero. -/
def EmptyMass (d : D) : Prop := blocksAdded d = 0 ∧ d.lh = 0 ∧ d.sumUpd = false

/-- Ordinary steps keep both the half-row mass and its reference scale. -/
def Retained (old d : D) : Prop :=
  blocksAdded d = blocksAdded old ∧ d.lh = old.lh ∧ d.sumUpd = old.sumUpd ∧
    reference d = reference old

/-- An actual vote followed by the probability arithmetic adds the current block. -/
def Added (L : Launch) (g : Nat) (old d : D) (e : Event) : Prop :=
  old.site = .rescaleVote ∧ blocksAdded d = old.block + 1 ∧
    ∃ mode mask arg take mid out, e.kind = .voteMode mode mask arg take ∧
      afterReferenceVote old take = some mid ∧
      probabilityUpdate L g {mid with voteTaken := take} = some out ∧
      d.lh = out.lh ∧ d.sumUpd = out.sumUpd ∧ reference d = reference out

private theorem initialized (P : Params) (L : Launch) (g : Nat) : EmptyMass (Wg0.init P L g) := by
  simp only [EmptyMass, blocksAdded, Wg0.init, firstSite, afterSink, afterLen]
  split_ifs <;> simp_all [updated]


private theorem peer_fields {d d' : D} {v : Value} (h : withPeerMax L d v = some d') :
    d'.lh = d.lh ∧ d'.sumUpd = d.sumUpd ∧ reference d' = reference d := by
  unfold withPeerMax at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 3500000 in
private theorem role_step {old d : D} {e : Event}
    (hn : Wg0.next P L g old e = some (some d)) :
    EmptyMass d ∨ Retained old d ∨ Added L g old d e := by
  cases hOld : old.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hOld] at hn
  case sink | lenOrig | lenExtra =>
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals left
    all_goals simp only [EmptyMass, blocksAdded, Wg0.init, afterSink, afterLen]
    all_goals (try split_ifs) <;> simp_all [updated]
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hm
        obtain ⟨hLh, hSum, hRef⟩ := peer_fields hv
        have hb := (peer_preserves_sub hv).1
        exact .inr (.inl ⟨by simp [blocksAdded, updated, hOld, hb], hLh, hSum, hRef⟩)
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · rename_i mode mask arg take hk
      obtain ⟨mid, hv, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨out, hp, rfl⟩ := Option.map_eq_some_iff.mp hm
      have hOldBlock := (vote_preserves_sub hv).1
      have hNewBlock := (probability_preserves_sub hp).1
      refine .inr (.inr ⟨hOld, ?_, mode, mask, arg, take, mid, out, hk, hv, hp, rfl, rfl, rfl⟩)
      simp only [blocksAdded, updated, ↓reduceIte, hNewBlock, hOldBlock]
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals right; left
  all_goals
    simp only [Retained, blocksAdded, updated, hOld, reference, loadScores, afterScoreSite,
      epiAfterBar, loadOutput]
  all_goals (try split_ifs) <;> simp_all

/-- A followed softmax state is initialized, retains the mass of its predecessor or adds one
block in the actual vote event. -/
theorem composed_step {q : Machine.ThreadD} {d : D} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) :
    EmptyMass d ∨ ∃ old, q = .wg0 old ∧ (Retained old d ∨ Added L g old d e) := by
  cases q
  case wg0 old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i a hnext
      cases hn
      rcases role_step hnext with hz | hs
      · exact .inl hz
      · exact .inr ⟨old, rfl, hs⟩
    · split at hn <;> cases hn
    · cases hn
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          exact .inl (initialized P L g)
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

/-- At every pre-epilogue vote the next numerical update is that state's block. -/
theorem blocksAdded_vote {d : D} (h : d.site = .rescaleVote) : blocksAdded d = d.block := by
  simp [blocksAdded, h, updated]

/-- Every epilogue state has already incorporated its last block. -/
theorem blocksAdded_epilogue {d : D} (h : d.site.inEpilogue = true) :
    blocksAdded d = d.block + 1 := by
  cases hs : d.site <;> simp_all [Wg0.Site.inEpilogue, blocksAdded, updated]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0MassHistory
