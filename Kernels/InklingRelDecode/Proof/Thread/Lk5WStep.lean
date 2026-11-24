-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5PeerStep
public import Kernels.InklingRelDecode.Proof.Thread.SmPeer

@[expose] public section

/-!
# `alpha` along the softmax region's steps

* `step_al`: a step from any site but `shfl5` keeps `alpha` (`D.stg.al`, `D.stg.alr`);
* `early_next`: a step from a site before the stage's second exchange (`Late` false) other than
  `shfl5` goes to such a site;
* `PostU`, `post_next`: the sites from the P store's barrier to the arrival; a step from one of them
  stays among them unless the iteration counter rises;
* `afterMax_al`: two states with the same shared numbers that receive each other's maximum have the
  same `alpha` after the shuffle.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lk

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The sites after the update of the running maximum: from `bar20` to the arrival. -/
def PostU : Site → Bool
  | .bar20 | .tmemSt | .tmemWait | .bar21 | .arrive => true
  | _ => false

/-- **A step from any site but `shfl5` keeps `alpha`.** -/
theorem step_al {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : next L g d e = some (some d'))
    (h5 : d.site ≠ .shfl5) : d'.stg.al = d.stg.al ∧ d'.stg.alr = d.stg.alr := by
  simp only [next, toBar20, afterArrive, afterSetup] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp_all; done)
    | (simp only [Option.some.injEq] at h; subst h
       first
         | exact ⟨rfl, rfl⟩
         | (split <;> exact ⟨rfl, rfl⟩)
         | simp [D.afterSum, D.upd])

theorem afterSetup_early {L : Launch} {g : Nat} {d d' : D}
    (h : afterSetup L g d = some (some d')) : Late d'.site = false := by
  unfold afterSetup at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; rfl)

/-- **A step from an early site other than `shfl5` stays early.** -/
theorem early_next {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) (hl : Late d.site = false) (h5 : d.site ≠ .shfl5) :
    Late d'.site = false := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [Late] at hl <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | exact afterSetup_early h
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; split <;> rfl)
    | (simp_all; done)

/-- **A step from a site after the update stays after it, or ends the iteration.** -/
theorem post_next {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) (hp : PostU d.site = true) (hi : d'.i = d.i) :
    PostU d'.site = true := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [PostU] at hp <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp_all; done)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (exfalso
       unfold afterArrive afterSetup at h
       split at h
       · simp at h
       · split at h <;> (simp only [Option.some.injEq] at h; subst h; simp at hi))

/-- The operand of the butterfly exchange at a site (`shfl7` to `shfl10`), and the word it sets
at the next site. -/
def bfOp (s : Site) (d : D) : Value :=
  match s with
  | .shfl7 => d.stg.al
  | .shfl8 => d.stg.cm1
  | .shfl9 => d.stg.cm2
  | _ => d.stg.cm3

/-- The site after a butterfly exchange. -/
def bfNext : Site → Site
  | .shfl7 => .shfl8
  | .shfl8 => .shfl9
  | .shfl9 => .shfl10
  | _ => .store10

/-- The word a butterfly exchange sets, read at the next site (`cm1` … `cm4`). -/
def bfRes (s : Site) (d : D) : Value :=
  match s with
  | .shfl7 => d.stg.cm1
  | .shfl8 => d.stg.cm2
  | .shfl9 => d.stg.cm3
  | _ => d.stg.cm4

/-- The butterfly sites. -/
def bfSite (s : Site) : Bool :=
  decide (s = .shfl7) || decide (s = .shfl8) || decide (s = .shfl9) || decide (s = .shfl10)

/-- **A step from a butterfly site**: the next site, the same iteration, and the minimum of the
operand and the received word. -/
theorem bf_next {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : next L g d e = some (some d'))
    (hs : bfSite d.site = true) :
    d'.site = bfNext d.site ∧ d'.i = d.i ∧
      ∃ (m : ShflMode) (a : Value) (b c : Nat) (r : Value) (o : Bool),
        e.kind = .shfl m a b c r o ∧ minE [bfOp d.site d, r] = .ok (bfRes d.site d') := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp [bfSite] at hs <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       exact ⟨rfl, rfl, _, _, _, _, _, _, by assumption, by assumption⟩)

/-- **The step into a butterfly result site comes from the butterfly site before it.** -/
theorem bf_prev {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : next L g d e = some (some d'))
    (hs : d'.site = .shfl8 ∨ d'.site = .shfl9 ∨ d'.site = .shfl10 ∨ d'.site = .store10) :
    bfSite d.site = true ∧ d'.site = bfNext d.site := by
  unfold next at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all [bfSite, bfNext]; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all [D.afterSum]; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all [D.afterMax, D.afterMaxT]; done)
    | (have := (toBar20_pf h).1; simp_all)
    | (have := afterSetup_pf h; unfold afterSetup at h; split at h <;> (try split at h) <;>
        simp only [Option.some.injEq] at h <;> (try subst h) <;> simp_all)
    | (unfold afterArrive afterSetup at h; split at h <;> (try split at h) <;>
        simp only [Option.some.injEq] at h <;> (try subst h) <;> simp_all)
    | (simp only [Option.some.injEq] at h; subst h; split <;> simp_all)

/-- **No step from a site after the update reaches `bar20`.** -/
theorem post_not_bar20 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) (hp : PostU d.site = true) : d'.site ≠ .bar20 := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [PostU] at hp <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp_all; done)
    | (simp only [Option.some.injEq] at h; subst h; simp)
    | (unfold afterArrive afterSetup at h
       split at h
       · simp at h
       · split at h <;> (simp only [Option.some.injEq] at h; subst h; simp))

/-- **A step from a site before the update to a site after it reaches `bar20`.** -/
theorem pre_to_post {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) (hl : Late d.site = true) (hp : PostU d.site = false)
    (hq : PostU d'.site = true) : d'.site = .bar20 := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [Late, PostU] at hl hp <;> simp only [next] at h <;>
    (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp_all; done)
    | exact (toBar20_pf h).1
    | (simp only [Option.some.injEq] at h; subst h; simp_all [PostU, D.afterSum])

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
