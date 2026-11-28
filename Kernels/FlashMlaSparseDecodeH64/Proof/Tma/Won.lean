-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref

@[expose] public section

/-! # The TMA warp's election in its ledger

After the election every count of the reference invariant holds one election (`elect_one`), and
the only site whose event is an election is the election site, at pc 2165 with the full mask
(`ev_elect`; a hand-back fires no event of its own). A step from a site after the election
stays after it and is no hand-back (`succ_post`); a losing lane's election step is the
hand-back (`succ_lose`). For the proof that the role's lane won its election
(`Common/TmaWon.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- **After the election the ledger holds one election.** -/
theorem elect_one {d : D} {n : Cnt → Nat} (hc : RefCore L g d n) (hs : d.site ≠ .elect) :
    n .elect = 1 := by
  tma_state d
  unfold RefCore at hc
  cases s <;> simp only [Site.inLoop, Bool.false_eq_true, ↓reduceIte] at hc
  case elect => exact absurd rfl hs
  case exit =>
    rcases hc with hc | hc <;> rw [hc .elect (by simp)] <;> simp [cntAt, proCnt, loopCnt]
  case outBar => rw [hc .elect (by simp)]; simp [cntAt, proCnt, loopCnt]
  all_goals first
    | (rw [hc.2 .elect (by simp)]; simp [cntAt, proCnt, loopCnt])
    | (rw [hc .elect (by simp)]; simp [cntAt, proCnt, loopCnt, Site.pro])

/-- **An election event is the election site's**, at pc 2165 with the full mask. -/
theorem ev_elect {d : D} {pc mk inst ld : Nat} (hl : ∀ s, d.site ≠ .leave s)
    (hev : Ev L g d ⟨pc, .elect mk inst ld⟩) :
    d.site = .elect ∧ pc = 2165 ∧ mk = 2 ^ 32 - 1 := by
  obtain ⟨hpc, hk⟩ := hev
  tma_state d
  simp only at hpc hk
  cases s <;> simp [EvK, Poll, RdAt] at hk
  case elect => exact ⟨rfl, hpc, by omega⟩
  case leave s => exact absurd rfl (hl s)

/-- A site after the election that is no hand-back. -/
def Post (s : Site) : Prop := s ≠ .elect ∧ ∀ i, s ≠ .leave i

/-- **A step from a site after the election stays after it.** -/
theorem succ_post {d d' : D} {f : Event} (hs : Post d.site)
    (h : succ P L g d f = some (some d')) : Post d'.site := by
  obtain ⟨hs, hl⟩ := hs
  tma_state d
  cases s <;> simp only [succ, ncWord, rdAny, word32, poll, afterQuad] at h
  case elect => exact absurd rfl hs
  case leave i => exact absurd rfl (hl i)
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals simp [Post, afterTopk, lensD, loopEntry, loopEnd, afterCoord, afterGather]
  all_goals (split_ifs <;> simp)

/-- **A losing lane's election step is the hand-back.** -/
theorem succ_lose {d d' : D} (hs : d.site = .elect) {pc mk inst ld : Nat}
    (hld : PTX.laneOf L g ≠ ld) (h : succ P L g d ⟨pc, .elect mk inst ld⟩ = some (some d')) :
    d' = { d with site := .leave (idleFirst P L g) } := by
  tma_state d
  simp only at hs
  subst hs
  simp only [succ, electNext, hld, ↓reduceIte, Option.some.injEq] at h
  exact h.symm

/-- **The elected lane's first state after the election** is after it, with the extra length
word of the parameters. -/
theorem lead_post (d : D) :
    Post (leadNext P L g d).site ∧ (leadNext P L g d).l1 = pw P.extra_topk := by
  unfold leadNext afterTopk lensD
  split_ifs <;> simp [Post]

/-- **A step keeps the extra length word** except at the election and the extra length load. -/
theorem l1_step {d a : D} {f : Event} (he : d.site ≠ .elect) (hx : d.site ≠ .loadExtra)
    (h : succ P L g d f = some (some a)) : a.l1 = d.l1 := by
  tma_state d
  cases s <;> simp only [succ, ncWord, rdAny, word32, poll, afterQuad] at h
  case elect => exact absurd rfl he
  case loadExtra => exact absurd rfl hx
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals simp [afterTopk, lensD, loopEntry, loopEnd]
  all_goals (split_ifs <;> simp)

/-- **Only a gather issues a tensor load.** -/
theorem ev_gather {d : D} {e : Event} {a : Nat} {s : TensorCopy.Spec}
    (hl : ∀ i, d.site ≠ .leave i) (hev : Ev L g d e) (hk : e.kind = .tensorIssue a s) :
    ∃ k, d.site = .gather k := by
  obtain ⟨-, hK⟩ := hev
  tma_state d
  cases s <;> simp [EvK, Poll, RdAt, hk] at hK
  case gather k => exact ⟨k, rfl⟩
  case leave i => exact absurd rfl (hl i)

/-- **Only the two arrival sites arrive.** -/
theorem ev_arrive {d : D} {e : Event} {l : Loc} {tx c : Nat} {r : Bool} {sc : MbarScope}
    (hl : ∀ i, d.site ≠ .leave i) (hev : Ev L g d e) (hk : e.kind = .arrive l tx c r sc) :
    d.site = .rawArrive ∨ d.site = .coordFree := by
  obtain ⟨-, hK⟩ := hev
  tma_state d
  cases s <;> simp [EvK, Poll, RdAt, hk] at hK
  case rawArrive => exact .inl rfl
  case coordFree => exact .inr rfl
  case leave i => exact absurd rfl (hl i)

/-- **A step keeps both length words** off the election and the two length loads, and never
returns to a length load. -/
theorem words_step {d a : D} {f : Event} (he : d.site ≠ .elect) (ht : d.site ≠ .loadTopk)
    (hx : d.site ≠ .loadExtra) (h : succ P L g d f = some (some a)) :
    a.l0 = d.l0 ∧ a.l1 = d.l1 ∧ a.site ≠ .loadTopk ∧ a.site ≠ .loadExtra := by
  tma_state d
  cases s <;> simp only [succ, ncWord, rdAny, word32, poll, afterQuad] at h
  case elect => exact absurd rfl he
  case loadTopk => exact absurd rfl ht
  case loadExtra => exact absurd rfl hx
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals simp [loopEntry, loopEnd, afterCoord, afterGather]
  all_goals (split_ifs <;> simp)

/-- **Only the CTA barrier steps to the exit** after the election. -/
theorem succ_exit {d a : D} {f : Event} (hs : Post d.site) (h : succ P L g d f = some (some a))
    (hx : a.site = .exit) : d.site = .outBar := by
  obtain ⟨hs, hl⟩ := hs
  tma_state d
  cases s <;> simp only [succ, ncWord, rdAny, word32, poll, afterQuad] at h
  case elect => exact absurd rfl hs
  case leave i => exact absurd rfl (hl i)
  case outBar => rfl
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals simp [afterTopk, lensD, loopEntry, loopEnd, afterCoord, afterGather] at hx
  all_goals split_ifs at hx

/-- **Only the exit site exits.** -/
theorem ev_exit {d : D} {e : Event} (hl : ∀ i, d.site ≠ .leave i) (hev : Ev L g d e)
    (hk : e.kind = .exit) : d.site = .exit := by
  obtain ⟨-, hK⟩ := hev
  tma_state d
  cases s <;> simp [EvK, Poll, RdAt, hk] at hK
  case exit => rfl
  case leave i => exact absurd rfl (hl i)

/-- **The elected lane of a CTA inside the batch** goes to a length load or the wait on
`bar_q_utccp`. -/
theorem lead_site (d : D) (hb : Arith32.scmp .ge .s (r2W L g) (pw P.b) = false) :
    (leadNext P L g d).site = .loadTopk ∨ (leadNext P L g d).site = .loadExtra ∨
      (leadNext P L g d).site = .qWait := by
  unfold leadNext afterTopk lensD
  simp only [hb, Bool.false_eq_true, ite_false]
  split_ifs <;> simp

/-- The elected lane of a CTA inside the batch does not exit at once. -/
theorem lead_ne_exit (d : D) (hb : Arith32.scmp .ge .s (r2W L g) (pw P.b) = false) :
    (leadNext P L g d).site ≠ .exit := by
  rcases lead_site d hb with h | h | h <;> rw [h] <;> simp

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
