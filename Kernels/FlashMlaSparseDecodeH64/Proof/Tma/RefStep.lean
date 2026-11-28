-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefArith

@[expose] public section

/-! # The TMA warp's reference invariant across one step: the tools

`RefCore` at a prologue site and at a loop site (`core_pro`, `core_loop`); the objects of the event
table as the launch's objects for the block's slots (`ready_of`, `free_of`, …); a step from a
prologue or loop place to the next (`pro_to`, `loop_to`), a poll's two outcomes (`pro_wait`,
`loop_wait`), and an event of a state with a successor is at a pc of the role (`inRole_next`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- A prologue site: neither in the loop nor the barrier or the exit. -/
def ProSite (s : Site) : Prop := s.inLoop = false ∧ s ≠ .exit ∧ s ≠ .outBar

theorem core_pro {d : D} {n : Cnt → Nat} (h : ProSite d.site) :
    RefCore L g d n ↔ ∀ c, c ≠ .ub → n c = cntAt (objs L g) d.site.pro 0 0 0 0 false c := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold RefCore
  split
  · contradiction
  · contradiction
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]

theorem core_loop {d : D} {n : Cnt → Nat} (h : d.site.inLoop = true) :
    RefCore L g d n ↔ LoopOk d ∧
      ∀ c, c ≠ .ub →
        n c = cntAt (objs L g) 3 d.cnt.toNat d.site.stage d.site.rdN d.site.gN false c := by
  unfold RefCore
  split
  · rename_i hs; rw [hs] at h; cases h
  · rename_i hs; rw [hs] at h; cases h
  · simp only [h, ↓reduceIte]

/-! ### The objects -/

theorem qUt_eq : (objs L g).qUt = smLoc L g (qUtW L) 0 := by unfold objs qUtL; rfl
theorem last_eq : (objs L g).last = smLoc L g (lastW L) 0 := by unfold objs lastL; rfl

section
variable {d : D} {b : Nat}

theorem ready_of (h : d.slot = W b) : smLoc L g (readyW L d) 0 = (objs L g).ready b := by
  unfold objs readyL; dsimp only; rw [← h]
theorem cfree_of (h : d.slot = W b) : smLoc L g (cfreeW L d) 0 = (objs L g).cfree b := by
  unfold objs cfreeL; dsimp only; rw [← h]
theorem free_of (h : d.buf = W b) : smLoc L g (freeW L d) 0 = (objs L g).free b := by
  unfold objs freeL; dsimp only; rw [← h]
theorem raw_of (h : d.buf = W b) : smLoc L g (rawW L d) 0 = (objs L g).raw b := by
  unfold objs rawL; dsimp only; rw [← h]
end

/-! ### Steps -/

/-- A prologue step to a prologue site. -/
theorem pro_to {d d' : D} {n : Cnt → Nat} {e : Event} {X : Option Cnt}
    (hpc : inRole e = true) (hk : kindOf e = X) (hd : ProSite d.site) (hd' : ProSite d'.site)
    (hJ : RefCore L g d n)
    (hc : ∀ c, plus (cntAt (objs L g) d.site.pro 0 0 0 0 false) X c =
      cntAt (objs L g) d'.site.pro 0 0 0 0 false c) :
    RefCore L g d' (Code.bump cls n e) :=
  (core_pro hd').2 (bump_kind hpc ((core_pro hd).1 hJ) fun c _ => hk ▸ hc c)

/-- A step inside a block that keeps the loop's words. -/
theorem loop_to {d d' : D} {n : Cnt → Nat} {e : Event} {X : Option Cnt}
    (hpc : inRole e = true) (hk : kindOf e = X) (hd : d.site.inLoop = true)
    (hd' : d'.site.inLoop = true) (hw : LoopOk d → LoopOk d') (hcnt : d'.cnt = d.cnt)
    (hJ : RefCore L g d n)
    (hc : ∀ c, plus (cntAt (objs L g) 3 d.cnt.toNat d.site.stage d.site.rdN d.site.gN false) X c =
      cntAt (objs L g) 3 d.cnt.toNat d'.site.stage d'.site.rdN d'.site.gN false c) :
    RefCore L g d' (Code.bump cls n e) := by
  obtain ⟨hL, hn⟩ := (core_loop hd).1 hJ
  refine (core_loop hd').2 ⟨hw hL, ?_⟩
  rw [hcnt]
  exact bump_kind hpc hn fun c _ => hk ▸ hc c

/-- The class of a poll: its object's when it succeeds, none when it fails. -/
theorem kindOf_poll {e : Event} {l : Loc} {q : Nat} {ok : Bool} {sc : MbarScope}
    (h : e.kind = .wait l q ok true sc) : kindOf e = if ok then some (.acq l) else none := by
  cases ok <;> simp [kindOf, h]

/-- A poll's successor: its site when it succeeds, the state when it fails. -/
theorem poll_eq {d d' e} {d₁ : D} {l : Loc} {q : Nat} {ok : Bool} {sc : MbarScope}
    (hk : e.kind = .wait l q ok true sc) (h : poll d e d₁ = some (some d')) :
    d' = if ok then d₁ else d := by
  simp only [poll, hk, Option.some.injEq] at h
  exact h.symm

/-- A poll at a prologue site to a prologue site. -/
theorem pro_wait {d d' d₁ : D} {n : Cnt → Nat} {e : Event} {l : Loc} {q : Nat} {ok : Bool}
    {sc : MbarScope} (hpc : inRole e = true) (hk : e.kind = .wait l q ok true sc)
    (hd : ProSite d.site) (h₁ : ProSite d₁.site) (hJ : RefCore L g d n)
    (hn : poll d e d₁ = some (some d'))
    (hc : ∀ c, plus (cntAt (objs L g) d.site.pro 0 0 0 0 false) (some (.acq l)) c =
      cntAt (objs L g) d₁.site.pro 0 0 0 0 false c) :
    RefCore L g d' (Code.bump cls n e) := by
  rw [poll_eq hk hn]
  have hK := kindOf_poll hk
  cases ok
  · exact pro_to hpc hK hd hd hJ fun c => by simp [plus_none']
  · exact pro_to hpc hK hd h₁ hJ hc

/-- A poll at a loop site to a loop site with the same words. -/
theorem loop_wait {d d' : D} {s : Site} {n : Cnt → Nat} {e : Event} {l : Loc} {q : Nat}
    {ok : Bool} {sc : MbarScope} (hpc : inRole e = true) (hk : e.kind = .wait l q ok true sc)
    (hd : d.site.inLoop = true) (hs : s.inLoop = true) (hJ : RefCore L g d n)
    (hn : poll d e { d with site := s } = some (some d'))
    (hc : ∀ c, plus (cntAt (objs L g) 3 d.cnt.toNat d.site.stage d.site.rdN d.site.gN false)
      (some (.acq l)) c = cntAt (objs L g) 3 d.cnt.toNat s.stage s.rdN s.gN false c) :
    RefCore L g d' (Code.bump cls n e) := by
  rw [poll_eq hk hn]
  have hK := kindOf_poll hk
  cases ok
  · exact loop_to hpc hK hd hd id rfl hJ fun c => by simp [plus_none']
  · exact loop_to (d' := { d with site := s }) hpc hK hd hs id rfl hJ hc

/-- The sites but the exit and the hand-back are at pcs of the role. -/
theorem site_inRole {s : Site} (h1 : s ≠ .exit) (h2 : ∀ i, s ≠ .leave i) :
    2165 ≤ s.pc ∧ s.pc ≤ 2330 := by
  cases s with
  | exit => exact absurd rfl h1
  | leave i => exact absurd rfl (h2 i)
  | coord0 k | coord1 k | coord2 k | coord3 k =>
    have := k.isLt; simp only [Site.pc, coordPc]; split_ifs <;> omega
  | gather k => have := k.isLt; simp only [Site.pc]; split_ifs <;> omega
  | _ => decide

/-- **An event a state follows is at a pc of the role.** -/
theorem inRole_next {d d' : D} {e : Event} (hpc : e.pc = d.site.pc)
    (hn : succ P L g d e = some (some d')) : inRole e = true := by
  have h1 : d.site ≠ .exit := fun h => by simp [succ, h] at hn
  have h2 : ∀ i, d.site ≠ .leave i := fun i h => by simp [succ, h] at hn
  have := site_inRole h1 h2
  simp only [inRole, hpc, decide_eq_true_eq]
  exact this

/-- A length load's successor is the transition at the word. -/
theorem word_next {e : Event} {f : BitVec 64 → D} {d' : D}
    (h : ncWord e f = some (some d')) : ∃ x, d' = f x := by
  unfold ncWord at h
  split at h
  · split at h
    · unfold word32 at h
      split at h
      · exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
      · cases h
    · cases h
  · cases h

/-- A coordinate element's successor is the transition at some value. -/
theorem rd_next {e : Event} {f : Value → D} {d' : D}
    (h : rdAny e f = some (some d')) : ∃ v, d' = f v := by
  unfold rdAny at h
  split at h
  · exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
  · cases h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
