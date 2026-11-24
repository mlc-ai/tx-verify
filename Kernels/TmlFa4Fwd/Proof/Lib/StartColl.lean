-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Start0
public import Kernels.TmlFa4Fwd.Proof.Lib.CollKind
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The startup's elections before a site -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

/-- The startup's elections of warp `w`. -/
def startEl (w : Nat) : Nat := if w = 0 then 16 else 0

/-- The startup's elections of warp `w` before a site. -/
def startCnt (w : Nat) : Startup.Site → Nat
  | .sh _ => 0
  | .elect j => if w = 0 then j.val else 0
  | .init q => if w = 0 then [1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
      11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16].getD q.val 0 else 0
  | .fence | .bar => startEl w
  | .enter _ => 0

theorem first_tab : ∀ j : Fin 16, startCnt 0 (Startup.firstInit j) = j.val + 1 ∧
    startCnt 0 (Startup.afterSite j) = j.val + 1 := by decide

theorem init_tab : ∀ q : Fin 34, (match Startup.initSucc q with
    | .elect j => startCnt 0 (.init q) == j.val + 1
    | s => startCnt 0 s == startCnt 0 (.init q)) = true := by decide

theorem cnt_ne {w : Nat} (h : w ≠ 0) (s : Startup.Site) : startCnt w s = 0 := by
  cases s <;> simp [startCnt, startEl, h]

theorem not_ne : Epilogue.scmpi .ne .b (BitVec.ofNat 64 0) 0 = false := by decide

theorem after0 {d : Startup.D} (h : d.x3 = BitVec.ofNat 64 0) (j : Fin 16) :
    (Startup.afterBlock d j).site = Startup.afterSite j := by
  unfold Startup.afterBlock
  rw [h, not_ne]
  rfl

/-- **A startup step of a lane of warp 0 and its elections.** -/
theorem startCnt_step0 {s s' : Startup.D} {n n' : Cls → Nat} {e : Event}
    (hS : StartAt0 L s n) (hev : Startup.Ev L g s e)
    (hub : ∀ f, e.kind ≠ .ub f) (hn : Startup.succ L g s e = some (some s'))
    (hS' : StartAt0 L s' n') :
    startCnt 0 s'.site = startCnt 0 s.site + if roundColl e then 1 else 0 := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨r, o, hk⟩ := hev <;> subst hk <;>
      simp only [Startup.succ, Startup.word32] at hn <;> split at hn <;>
      simp only [Option.some.injEq, reduceCtorEq] at hn <;> subst hn
    · rfl
    · rfl
    · split at hS'
      · rename_i x hx
        simp only [StartAt0] at hS'
        obtain ⟨-, -, h3⟩ := hS'
        rw [h3, not_ne] at hx
        cases hx
      · rename_i x hx
        simp only [hx]
        rfl
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨i, ld, -, hk⟩ | ⟨f, hk⟩
    swap
    · exact absurd hk (hub f)
    subst hk
    simp only [Startup.succ, Option.some.injEq] at hn
    have h3 : x3 = BitVec.ofNat 64 0 := hS.2.2
    subst hn
    obtain ⟨t1, t2⟩ := first_tab j
    show startCnt 0 _ = j.val + 1
    split
    · exact t1
    · rw [after0 h3]; exact t2
  | init q =>
    have hr : roundColl ⟨pc, kind⟩ = false := by
      simp only [Startup.Ev] at hev
      rcases hev with ⟨l, c, hk⟩ | ⟨f, hk⟩
      · subst hk; rfl
      · exact absurd hk (hub f)
    rw [hr]
    have h3 : x3 = BitVec.ofNat 64 0 := hS.2.2
    have ht := init_tab q
    simp only [Startup.succ] at hn
    split at hn
    · rename_i j hj
      rw [hj] at ht
      simp only [Option.some.injEq] at hn
      subst hn
      rw [after0 h3]
      exact (first_tab j).2.trans (beq_iff_eq.mp ht).symm
    · rename_i hne
      simp only [Option.some.injEq] at hn
      subst hn
      show startCnt 0 (Startup.initSucc q) = startCnt 0 (.init q)
      revert ht hne
      cases Startup.initSucc q <;> intro ht hne <;> first
        | exact beq_iff_eq.mp ht
        | exact absurd rfl (hne _)
  | fence =>
    simp only [Startup.Ev] at hev
    subst hev
    simp only [Startup.succ, Option.some.injEq] at hn
    subst hn
    rfl
  | bar =>
    exfalso
    simp only [Startup.succ, Option.some.injEq] at hn
    subst hn
    obtain ⟨r, hr⟩ := enterOf_isEnter ⟨.bar, x1, x2, x3⟩
    simp only [StartAt0, hr] at hS'
  | enter r => simp [Startup.succ] at hn

/-- Only the barrier leads to a role. -/
theorem bar_of_enter {s s' : Startup.D} {e : Event} {r : Startup.Entry}
    (hn : Startup.succ L g s e = some (some s')) (hr : s'.site = .enter r) : s.site = .bar := by
  have mid : ∀ {x : Startup.Site}, x.mid = true → x ≠ .enter r := by
    rintro x h rfl; cases h
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | sh j =>
    exfalso
    fin_cases j <;> cases kind <;> simp only [Startup.succ, Startup.word32, reduceCtorEq] at hn <;>
      split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn <;> subst hn
    · cases hr
    · cases hr
    · split at hr <;> cases hr
  | elect j =>
    exfalso
    cases kind <;> simp only [Startup.succ, Option.some.injEq, reduceCtorEq] at hn
    subst hn
    split at hr
    · exact mid (mid_firstInit j) hr
    · exact mid (mid_afterBlock _ j) hr
  | init q =>
    exfalso
    simp only [Startup.succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact mid (mid_afterBlock _ _) hr
    · simp only [Option.some.injEq] at hn
      subst hn
      exact mid (mid_initSucc q) hr
  | fence =>
    simp only [Startup.succ, Option.some.injEq] at hn
    subst hn
    cases hr
  | bar => rfl
  | enter r => simp [Startup.succ] at hn

end
end PTX.Kernels.TmlFa4Fwd.Proof
