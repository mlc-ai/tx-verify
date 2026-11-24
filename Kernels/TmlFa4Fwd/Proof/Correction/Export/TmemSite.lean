-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemCol
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Correction.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemStore
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction Tensor Memory site on the trace: the counts of its place, and what follows a
store -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The P-full arrivals of stage `st` at a site, as rounds done `r`: `1 + r`. -/
def arrOk (st : Fin 2) (s : Site) : Bool :=
  decide ((arrivePts (96 + 8 * st.val)).countP (before s) = 1)

theorem tab : (List.finRange 2).all (fun st =>
    decide ((arrivePts (96 + 8 * st.val)).countP inRound = 1) &&
    (List.finRange 8).all (fun c => arrOk st (.rld st c) && arrOk st (.rst st c)) &&
    (List.finRange 16).all fun j => arrOk st (.fld st j)) = true := by
  decide +kernel

/-- The trace's P-full arrivals at a state. -/
theorem pArr_at {k : Nat} {d : Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n))) (st : Nat) :
    Tm.pArr L X g st k = n (.corr (.arrive (96 + 8 * st))) := by
  rw [← count hσ]
  rfl

/-- **The P-full arrivals before a load or store of stage `st`**: the first and one per round. -/
theorem site_arr {k : Nat} {d : Control.D} {n : Cls → Nat} {r ℓ : Nat} {st : Fin 2}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hQ : RefQ p L g d (CorrWarp.rc n) r ℓ)
    (hs : (∃ c, d.site = .rld st c) ∨ (∃ c, d.site = .rst st c) ∨ ∃ j, d.site = .fld st j) :
    Tm.pArr L X g st k = 1 + r := by
  have h := hQ.cnt (.arrive (96 + 8 * st.val)) (by simp)
  rw [pArr_at hσ]
  have ht := List.all_eq_true.mp tab st (List.mem_finRange st)
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨h1, h2⟩, h3⟩ := ht
  refine Eq.trans h ?_
  have hb : (arrivePts (96 + 8 * st.val)).countP (before d.site) = 1 := by
    rcases hs with ⟨c, hs⟩ | ⟨c, hs⟩ | ⟨c, hs⟩ <;> rw [hs]
    · exact of_decide_eq_true (h2 c (List.mem_finRange c)).1
    · exact of_decide_eq_true (h2 c (List.mem_finRange c)).2
    · exact of_decide_eq_true (h3 c (List.mem_finRange c))
  show (arrivePts (96 + 8 * st.val)).countP _ + r * (arrivePts (96 + 8 * st.val)).countP _ = _
  rw [show d.scheduler.site = d.site from rfl, hb, h1]
  omega

/-! ### After a store -/

/-- The place of a state in stage `st`'s rescale loop. -/
def stPos (st : Fin 2) : Site → Nat
  | .rld s c => if s = st then 3 * c.val + 1 else 0
  | .rldw s c => if s = st then 3 * c.val + 2 else 0
  | .rst s c => if s = st then 3 * c.val + 3 else 0
  | .rwait s => if s = st then 25 else 0
  | .rarr s k => if s = st ∧ k = 0 then 26 else 0
  | _ => 0

theorem stPos_next {st : Fin 2} {d d' : D} {e : Event} (h1 : 1 ≤ stPos st d.site)
    (h2 : stPos st d.site ≤ 25) (hn : succ p L g d e = some (some d')) :
    stPos st d'.site = stPos st d.site + 1 := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> (try simp only [stPos, Nat.le_zero, Nat.one_ne_zero, Nat.not_succ_le_zero] at h1)
  case rld s c =>
    simp only [succ] at hn
    split_ifs at hn
    · split at hn
      · split at hn
        · cases hn; simp only [stPos]; split_ifs <;> simp_all
        · cases hn
      · cases hn
    · cases hn
  case rldw s c =>
    simp only [succ] at hn
    split_ifs at hn
    · cases hn; simp only [stPos, D.mk']; split_ifs <;> simp_all
    · cases hn
  case rst s c =>
    have hs : s = st := by by_contra h; simp [h] at h1
    subst hs
    simp only [succ] at hn
    split_ifs at hn with h7
    · cases hn; simp [stPos, D.mk', h7]
    · cases hn
      simp only [stPos, D.mk', ↓reduceIte]
      have : (c + 1).val = c.val + 1 := by
        have := c.isLt
        rw [Fin.val_add_one_of_lt' (by omega)]
      omega
  case rwait s =>
    have hs : s = st := by by_contra h; simp [h] at h1
    subst hs
    simp only [succ, Option.some.injEq] at hn
    subst hn
    simp [stPos, D.mk']
  case rarr s k =>
    exfalso
    simp only [stPos] at h1 h2
    split_ifs at h1 h2 <;> omega

theorem stPos_shape {st : Fin 2} {d : Control.D} {e : Event} (hp : 1 ≤ stPos st d.site)
    (h : Control.Ev p L g d e) : Ev p L g d.scheduler e := by
  obtain ⟨s,v,k⟩ := d
  cases s <;> first | exact h | cases hp

theorem stPos_next_control {st : Fin 2} {d d' : Control.D} {e : Event}
    (h1 : 1 ≤ stPos st d.site) (h2 : stPos st d.site ≤ 25)
    (hn : Control.succ p L g d e = some (some d')) :
    stPos st d'.site = stPos st d.site + 1 := by
  have direct (hs : (succ p L g d.scheduler e).map (Option.map Control.erase) = some (some d')) :
      stPos st d'.site = stPos st d.site + 1 := by
    obtain ⟨x,hx,hm⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨a,rfl,rfl⟩ := Option.map_eq_some_iff.mp hm
    exact stPos_next (d := d.scheduler) h1 h2 hx
  obtain ⟨s,v,k⟩ := d
  cases s <;> try exact direct hn
  all_goals try cases h1
  case rld s c =>
    simp only [Control.succ] at hn
    split at hn
    · cases hn
      simp only [stPos]
      split_ifs <;> simp_all [stPos]
    · cases hn

/-- The events of stage `st`'s rescale loop: `tcgen05` events up to the wait, then the P-full
arrival. -/
theorem stPos_ev {st : Fin 2} {d : D} {e : Event} (h1 : 1 ≤ stPos st d.site)
    (hev : Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f) :
    (stPos st d.site ≤ 25 → ∃ tk, e.kind = .tc tk) ∧
      (stPos st d.site = 25 → e.kind = .tc .waitSt) ∧
      (stPos st d.site = 26 → arrivesOn (Tm.pFull L (g / L.block) st) e = true) := by
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hub
  cases s <;> (try simp only [stPos, Nat.le_zero, Nat.one_ne_zero, Nat.not_succ_le_zero] at h1)
  case rld s c =>
    have hs : s = st := by by_contra h; simp [h] at h1
    subst hs
    have := c.isLt
    simp only [Ev] at hev
    refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_⟩
    · rcases hev with ⟨_, _, _, h⟩ | ⟨f, h⟩
      · exact ⟨_, h⟩
      · exact absurd h (hub f)
    all_goals simp [stPos] at h; omega
  case rldw s c =>
    have hs : s = st := by by_contra h; simp [h] at h1
    subst hs
    have := c.isLt
    simp only [Ev] at hev
    refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_⟩
    · rcases hev with h | ⟨_, _, _, h⟩ | ⟨f, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact absurd h (hub f)
    all_goals simp [stPos] at h; omega
  case rst s c =>
    have hs : s = st := by by_contra h; simp [h] at h1
    subst hs
    have := c.isLt
    simp only [Ev] at hev
    refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_⟩
    · rcases hev with ⟨_, _, _, h⟩ | ⟨f, h⟩
      · exact ⟨_, h⟩
      · exact absurd h (hub f)
    all_goals simp [stPos] at h; omega
  case rwait s =>
    have hs : s = st := by by_contra h; simp [h] at h1
    subst hs
    simp only [Ev] at hev
    have hk : kd = .tc .waitSt := by
      rcases hev with h | ⟨f, h⟩
      · exact h
      · exact absurd h (hub f)
    exact ⟨fun _ => ⟨_, hk⟩, fun _ => hk, fun h => by simp [stPos] at h⟩
  case rarr s k =>
    have hs : s = st ∧ k = 0 := by by_contra h; simp [h] at h1
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨fun h => by simp [stPos] at h, fun h => by simp [stPos] at h, fun _ => ?_⟩
    simp only [Ev] at hev
    subst hev
    fin_cases s <;> simp [arrivesOn, sourceArrive, Tm.pFull, Tm.bar, arrOff]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
