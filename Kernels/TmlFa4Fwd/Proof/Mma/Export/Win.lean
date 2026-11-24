-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Events
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Pred
import Lemmas.Kernel.ElectSource
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's issues and commits are one lane's

The MMA issue sites, the PV block's poll after a winner's MMA and the commits (`winSite`) are
entered only from such a site or on an election the lane won (`pred_win`), so a lane at such a
state has won an election (`win_states`, `won_elect`). Two elections of one warp with the full
mask return one leader (`elect_winner`), so two lanes of warp 12 of a CTA at such states are one
lane (`win_lane`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites only an election winner reaches. -/
def winSite : Mma.Site → Bool
  | .qk _ _ | .pv _ _ | .cm _ => true
  | .mw _ l => l
  | _ => false
theorem qkDone_nw (b : Fin 4) : winSite (Mma.qkDone b) = false := by fin_cases b <;> rfl
theorem pvDone_nw (b : Fin 4) : winSite (Mma.pvDone b) = false := by fin_cases b <;> rfl
theorem wtNext_nw (k : Fin 10) : winSite (Mma.wtNext k) = false := by fin_cases k <;> rfl
theorem shNext_nw (k : Fin 14) : winSite (Mma.shNext k) = false := by fin_cases k <;> rfl
theorem scanExit_nw {l : Bool} {d : Mma.D} {gx cur : BitVec 64} :
    winSite (Mma.scanExit p l d gx cur).site = false := by
  unfold Mma.scanExit; split <;> rfl
theorem loopHead_nw {l : Bool} {d : Mma.D}
    {grp acc : BitVec 64} : winSite (Mma.loopHead p L g l d grp acc).site = false := by
  unfold Mma.loopHead
  split
  · exact scanExit_nw
  · split <;> rfl
theorem afterTotal_nw {k : Epilogue.Scan} {d : Mma.D}
    {x : BitVec 64} : winSite (Mma.afterTotal p L g k d x).site = false := by
  cases k <;> unfold Mma.afterTotal <;> dsimp only <;> split <;>
    first | exact scanExit_nw | exact loopHead_nw
theorem afterTiles_nw {d d' : Mma.D} {x : BitVec 64}
    (h : Mma.afterTiles p L g d x = some d') : winSite d'.site = false := by
  simp only [Mma.afterTiles] at h
  repeat' split at h
  all_goals (cases h <;> (try split) <;> rfl)
theorem ceNext_nw {d : Mma.D} (c : Fin 12) :
    winSite (Mma.ceNext p L g d c).site = false := by
  fin_cases c <;> simp only [Mma.ceNext, Mma.enterLoop, Mma.loopEnd, Mma.passStart] <;>
    (repeat' split) <;> rfl

set_option maxHeartbeats 4000000 in
/-- **A winning site is entered from a winning site or on a won election.** -/
theorem pred_win {d d' : Mma.D} {e : Event}
    (hn : Mma.succ p L g d e = some (some d')) (hw : winSite d'.site = true) :
    winSite d.site = true ∨ ∃ m inst, e.kind = .elect m inst (laneOf L g) := by
  obtain ⟨s, v⟩ := d
  cases s
  case qk b j => exact .inl rfl
  case pv b j => exact .inl rfl
  case cm c => exact .inl rfl
  case eq b =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · rename_i h; subst h; exact .inr ⟨m, inst, heq⟩
      · rw [qkDone_nw] at hw; cases hw
    · cases hn
  case ep b =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · rename_i h; subst h; exact .inr ⟨m, inst, heq⟩
      · simp [winSite] at hw
    · cases hn
  case ce c =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · rename_i h; subst h; exact .inr ⟨m, inst, heq⟩
      · rw [ceNext_nw] at hw; cases hw
    · cases hn
  case mw b ld =>
    cases ld
    · exfalso
      simp only [Mma.succ] at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        split at hw
        · simp at hw; rw [pvDone_nw] at hw; cases hw
        · exact absurd hw (by simp [winSite])
      · cases hn
    · exact .inl rfl
  case total k =>
    exfalso
    simp only [Mma.succ, Mma.word32] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals (simp only [Option.some.injEq] at hn; subst hn; rw [afterTotal_nw] at hw; cases hw)
  case tiles l =>
    exfalso
    simp only [Mma.succ] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals first
      | (simp only [Option.some.injEq] at hn; subst hn; simp [winSite, Mma.scAt] at hw; done)
      | (obtain ⟨x, hx, hx2⟩ := Option.map_eq_some_iff.mp hn
         cases hx2
         rw [afterTiles_nw hx] at hw; cases hw)
  all_goals exfalso
  all_goals simp only [Mma.succ, Mma.word32, Mma.passStart, Option.map] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [winSite] at hw; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (rw [wtNext_nw] at hw; cases hw)
         | (rw [shNext_nw] at hw; cases hw)
         | (simp [winSite, Mma.scAt] at hw; (repeat' split at hw) <;> simp at hw))
    | skip

/-- **A lane at a winning state has won an election.** -/
theorem win_states (hX : Consistent L kernel Assumptions.all m X) :
    ∀ (k : Nat) (d : Mma.D) (n : Cls → Nat),
      Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)) →
      winSite d.site = true → 1 ≤ n (.mma .won) := by
  intro k
  induction k with
  | zero =>
    intro d n h _
    rw [Frame.stateAt_zero] at h
    simp [thread, glued, Code.counted, Code.glue, Code.enter, exit, Startup.code] at h
  | succ k ih =>
    intro d n h hw
    rcases hk : (X.tr g)[k]? with _ | e
    · have hle : (X.tr g).length ≤ k := by
        by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hk; cases hk
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hle] at h
      exact ih d n h hw
    · have hne : d ≠ (Mma.code p L g (Mma.ent p L)).init := by
        rintro rfl; simp [winSite, Mma.code] at hw
      obtain ⟨d0, n0, h0, hs0⟩ := mma_pred hk h hne
      -- the counts after the step
      have hn : n = Code.bump (Proof.cls L g) n0 e := by
        rw [Frame.stateAt_succ hk, h0] at h
        have h' : (thread p L g).next (Mma.minj p L g d0 n0) e =
            some (some (Mma.minj p L g d n)) := h
        have hs0' : (Mma.code p L g (Mma.ent p L)).next d0 e = some (some d) := hs0
        rw [Mma.next_minj, hs0'] at h'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
        exact h'.2.symm
      subst hn
      simp only [Code.bump]
      rcases pred_win hs0 hw with h1 | ⟨mk, inst, hk'⟩
      · have := ih d0 n0 h0 h1
        omega
      · have he : X.get (g, k) = some e := hk
        obtain ⟨pc, kind⟩ := e
        simp only at hk'
        subst hk'
        have hm := elect_full hX (show X.Elect (g, k) pc mk inst (laneOf L g) from he)
        subst hm
        simp [Proof.cls, Mma.cls]

/-- **A lane at a winning state has made an election it won**, with the full mask. -/
theorem won_elect (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {d : Mma.D}
    {n : Cls → Nat} (h : Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)))
    (hw : winSite d.site = true) :
    ∃ j pc inst, X.get (g, j) = some ⟨pc, .elect 4294967295 inst (laneOf L g)⟩ := by
  have h1 := win_states hX k d n h hw
  rw [← count h (.mma .won)] at h1
  obtain ⟨e, hmem, hc⟩ := List.countP_pos_iff.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem (List.mem_of_mem_take hmem)
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Proof.cls, Mma.cls] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨j, pc, _, by rw [← hget]; exact List.getElem?_eq_getElem hj⟩

/-- **Two lanes of one warp at winning states are one lane.** -/
theorem win_lane (hX : Consistent L kernel Assumptions.all m X) {h k k' : Nat} {d d' : Mma.D}
    {n n' : Cls → Nat} (hw : SameWarp L g h)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)))
    (hσ' : Frame.stateAt (thread p L) X h k' = some (some (Mma.minj p L h d' n')))
    (hs : winSite d.site = true) (hs' : winSite d'.site = true) : g = h := by
  obtain ⟨j, pc, inst, he⟩ := won_elect hX hσ hs
  obtain ⟨j', pc', inst', he'⟩ := won_elect hX hσ' hs'
  have hl := elect_winner (e := (g, j)) (f := (h, j')) hX he he' hw
  obtain ⟨⟨hg, hh, hc⟩, hwi⟩ := hw
  simp only [laneOf] at hl
  have h1 := Nat.div_add_mod g L.block
  have h2 := Nat.div_add_mod h L.block
  have h3 := Nat.div_add_mod (g % L.block) 32
  have h4 := Nat.div_add_mod (h % L.block) 32
  rw [hc] at h1
  rw [hwi] at h3
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
