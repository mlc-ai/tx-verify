-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkBase

@[expose] public section

/-!
# Warp lockstep: the prologue

The prologue's sites are declared in the order of the code and every successor is a later site, so
the key of a state is the next synchronizing position at or after its own (`siteKey`). Two sites
steer the successor by a value: `ptc0_3` and `ptc1_3` leave for the query loads when the next
pipeline stage is not preloaded (`ProA.v_p63`, `ProA.v_p72`, functions of the request's
`num_pre`), and `bar2` skips all three stages when none is (`ProA.v_p53`); their key is the key
of the branch taken. The branches are the same for the lanes of a warp when their data are the
same (`ProAgree`). The lane-dependent branches (the elected lane's copies, the guarded query
loads, the lane that arrives on the barrier) all lead to the same next synchronizing site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- The key of a prologue site: the next synchronizing position. -/
def siteKey (s : ProA.Site) : Nat := keyPc s.pc s.sub

/-- The key of the query loads and stores: they hold no synchronizing instruction. -/
def keyQ : Nat := siteKey .stq0_0

/-- The key of a prologue state. -/
def proKey (L : Launch) (g : Nat) (d : ProA.D) : Nat :=
  match d.site with
  | .ptc0_3 => if ProA.v_p63 L g d.dt then keyQ else siteKey .pbA1
  | .ptc1_3 => if ProA.v_p72 L g d.dt then keyQ else siteKey .pbA2
  | s => siteKey s

/-- The state's event is synchronizing. -/
def proSy (d : ProA.D) : Bool := syAt d.site.pc d.site.sub

/-- What two lanes' data agree on at a prologue state: the steering guards. -/
def ProAgree (L : Launch) (g h : Nat) (d d' : ProA.D) : Prop :=
  ProA.v_p53 L g d.dt = ProA.v_p53 L h d'.dt ∧ ProA.v_p63 L g d.dt = ProA.v_p63 L h d'.dt ∧
    ProA.v_p72 L g d.dt = ProA.v_p72 L h d'.dt

theorem proKey_q (L : Launch) (g : Nat) (dt dt' : ProA.Dat) (j : Nat) :
    proKey L g ⟨ProA.qSite L g dt j, dt'⟩ = keyQ := by
  unfold ProA.qSite
  split <;> (repeat' split) <;> simp only [proKey] <;> decide +kernel

theorem pro_sy_key (L : Launch) (g : Nat) {d : ProA.D} (h : proSy d = true) :
    proKey L g d = d.site.pc := by
  obtain ⟨s, dt⟩ := d
  simp only [proSy] at h
  cases s <;> simp only [proKey] <;>
    first | (exfalso; revert h; decide +kernel) | (revert h; decide +kernel)

theorem pro_silent {L : Launch} {g : Nat} {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) (hs : proSy d = false) :
    proKey L g d' = proKey L g d := by
  obtain ⟨s, dt⟩ := d
  simp only [proSy] at hs
  cases s <;> simp only [ProA.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       first
       | (exfalso; revert hs; decide +kernel)
       | ((try simp only [proKey_q]); simp only [proKey]; (repeat' split) <;>
          first | (revert hs; decide +kernel) | simp_all))

/-! ### Two lanes at one synchronizing site -/

theorem ofNat_ctorIdx (s : ProA.Site) : ProA.Site.ofNat s.ctorIdx = s := by
  cases s <;> rfl

theorem ctorIdx_lt (s : ProA.Site) : s.ctorIdx < 182 := by
  cases s <;> decide

theorem pc_inj_nat : ∀ n < 182, ∀ m < 182,
    syAt (ProA.Site.ofNat n).pc (ProA.Site.ofNat n).sub = true →
    syAt (ProA.Site.ofNat m).pc (ProA.Site.ofNat m).sub = true →
    (ProA.Site.ofNat n).pc = (ProA.Site.ofNat m).pc → n = m := by decide +kernel

/-- **Two synchronizing prologue states at one position are at one site.** -/
theorem pro_site_eq {d d' : ProA.D} (hs : proSy d = true) (hs' : proSy d' = true)
    (h : d.site.pc = d'.site.pc) : d.site = d'.site := by
  have h1 := pc_inj_nat d.site.ctorIdx (ctorIdx_lt _) d'.site.ctorIdx (ctorIdx_lt _)
    (by rw [ofNat_ctorIdx]; exact hs) (by rw [ofNat_ctorIdx]; exact hs')
    (by rw [ofNat_ctorIdx, ofNat_ctorIdx]; exact h)
  rw [← ofNat_ctorIdx d.site, ← ofNat_ctorIdx d'.site, h1]

theorem v_p63_elDt (L : Launch) (g : Nat) (dt : ProA.Dat) (pc : Nat) (b : Bool) :
    ProA.v_p63 L g (ProA.elDt dt pc b) = ProA.v_p63 L g dt := rfl

theorem v_p72_elDt (L : Launch) (g : Nat) (dt : ProA.Dat) (pc : Nat) (b : Bool) :
    ProA.v_p72 L g (ProA.elDt dt pc b) = ProA.v_p72 L g dt := rfl

theorem pro_step {L : Launch} {g h : Nat} {d d' : ProA.D} {e e' : Event} {t t' : ProA.D}
    (hs : proSy d = true) (hs' : proSy d' = true) (hk : proKey L g d = proKey L h d')
    (ha : ProAgree L g h d d')
    (hn : ProA.next L g d e = some (some t)) (hn' : ProA.next L h d' e' = some (some t')) :
    proKey L g t = proKey L h t' := by
  have hsite := pro_site_eq hs hs' (by rw [← pro_sy_key L g hs, ← pro_sy_key L h hs', hk])
  obtain ⟨s, dt⟩ := d
  obtain ⟨s', dt'⟩ := d'
  simp only [] at hsite
  subst hsite
  obtain ⟨a1, a2, a3⟩ := ha
  simp only [proSy] at hs hs'
  revert hs
  cases s <;> first | (intro hs; exfalso; revert hs; decide +kernel) | intro hs <;>
    simp only [ProA.next] at hn hn' <;> (repeat' split at hn) <;> (repeat' split at hn') <;>
    first
    | (simp at hn; done)
    | (simp at hn'; done)
    | (simp only [Option.some.injEq] at hn hn'; subst hn hn'
       ((try simp only [proKey_q]) <;> simp only [proKey] <;> (repeat' split) <;>
          first | (revert hs; decide +kernel) | simp_all [v_p63_elDt, v_p72_elDt]))

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
