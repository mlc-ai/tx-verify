-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkD
public import Kernels.InklingRelDecode.Proof.Thread.LkWStep
public import Kernels.InklingRelDecode.Proof.Thread.LkB0
public import Kernels.InklingRelDecode.Proof.Progress.WtMono
public import Kernels.InklingRelDecode.Proof.Progress.WtOrder

@[expose] public section

/-!
# The time of a key: the default partition

The key of a default-partition state (`dKey`) names the position of its next synchronizing
state and, in the softmax region, the iteration that state is in. `ktD` reads the virtual time
(`Wt.time`) of that synchronizing state off the key: the position picks the region (the common
start below 20, the prologue below 574, the softmax region below 2603, the epilogue above) and
the site, and the softmax region's time adds the slot of the key's iteration.

* `kxD_sy`: a synchronizing state's key time is its own time.
* `kxD_lt`: a state that is not synchronizing is timed below its key time, when its key is a
  synchronizing position (a state with no synchronizing state after it, the epilogue's `exit`,
  has its own position as its key).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

/-! ### The time of a synchronizing position -/

/-- The common start's synchronizing sites. -/
def dsSyncs : List DStart.Site := [.alloc, .bar0, .bar1, .relinq, .shfl]

/-- The time of a synchronizing position of the common start. -/
def dsTimeAt (pc : Nat) : Nat :=
  match dsSyncs.find? (fun s => s.pc == pc) with
  | some s => dstartT ⟨s, b32 0⟩
  | none => 0

/-- The index of the prologue's synchronizing site at a position. -/
def proIdxAt (pc : Nat) : Nat :=
  ((List.range 182).find? (fun n =>
    (ProA.Site.ofNat n).pc == pc && syAt (ProA.Site.ofNat n).pc (ProA.Site.ofNat n).sub)).getD 0

/-- The softmax region's time of a site in iteration `i` (`smT` without the other fields). -/
def smTS (s : Sm.Site) (i : Nat) : Nat :=
  match s with
  | .setMaxReg => c0 + 4
  | .bar0 => c1
  | .pre j => c1 + 4 + 4 * j.val
  | s => slot i + bandS + (90 - Bound.Sm.pos s)

theorem smT_eq (d : Sm.D) : smT d = smTS d.site d.i := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> rfl

/-- The time of a synchronizing position of the softmax region in iteration `i`. -/
def smTimeAt (pc i : Nat) : Nat :=
  match smSites.find? (fun s => s.pc == pc) with
  | some s => smTS s i
  | none => 0

/-- The epilogue's time of a site. -/
def epTS (s : Epi.Site) : Nat := epi0 + 4 * (75 - Bound.Epi.siteRank s)

/-- The time of a synchronizing position of the epilogue. -/
def epTimeAt (pc : Nat) : Nat :=
  match epSites.find? (fun s => s.pc == pc) with
  | some s => epTS s
  | none => 0

/-- **The time of a default-partition key.** -/
def ktD (k : Key) : Nat :=
  if k.1 < 20 then dsTimeAt k.1
  else if k.1 < 574 then 100 + proIdxAt k.1
  else if k.1 < 2603 then smTimeAt k.1 k.2.2.1
  else epTimeAt k.1

/-- The key time of a default-partition state. -/
def kxD (L : Launch) (g : Nat) (s : DComp.St) : Nat := ktD (dKey L g s)

/-! ### The common start -/

theorem ds_sy_time : ∀ s : DStart.Site, syAt s.pc s.sub = true → s ≠ .toProA →
    ktD (kOf (keyPc s.pc s.sub)) = dstartT ⟨s, b32 0⟩ := by
  intro s; cases s <;> decide +kernel

theorem ds_lt_time : ∀ s : DStart.Site, syAt s.pc s.sub = false → s ≠ .toProA →
    syPc (keyPc s.pc s.sub) = true → dstartT ⟨s, b32 0⟩ < ktD (kOf (keyPc s.pc s.sub)) := by
  intro s; cases s <;> decide +kernel

/-! ### The prologue -/

theorem pro_sy_nat : ∀ n < 182, syAt (ProA.Site.ofNat n).pc (ProA.Site.ofNat n).sub = true →
    20 ≤ (ProA.Site.ofNat n).pc ∧ (ProA.Site.ofNat n).pc < 574 ∧
      proIdxAt (ProA.Site.ofNat n).pc = n := by
  decide +kernel

/-- The time of a prologue site's key, for the sites whose key is their own `siteKey`. -/
def proLtOk (n : Nat) : Bool :=
  let k := siteKey (ProA.Site.ofNat n)
  !syPc k || (decide (20 ≤ k) && decide (k < 574) && decide (n < proIdxAt k))

theorem pro_lt_nat : ∀ n < 182, syAt (ProA.Site.ofNat n).pc (ProA.Site.ofNat n).sub = false →
    proLtOk n = true := by
  decide +kernel

theorem pro_branch_keys :
    (20 ≤ keyQ ∧ keyQ < 574 ∧ ProA.Site.ptc0_3.ctorIdx < proIdxAt keyQ ∧
      ProA.Site.ptc1_3.ctorIdx < proIdxAt keyQ) ∧
    (20 ≤ siteKey .pbA1 ∧ siteKey .pbA1 < 574 ∧
      ProA.Site.ptc0_3.ctorIdx < proIdxAt (siteKey .pbA1)) ∧
    (20 ≤ siteKey .pbA2 ∧ siteKey .pbA2 < 574 ∧
      ProA.Site.ptc1_3.ctorIdx < proIdxAt (siteKey .pbA2)) := by
  decide +kernel

theorem ktD_pro {k : Nat} (h1 : 20 ≤ k) (h2 : k < 574) : ktD (kOf k) = 100 + proIdxAt k := by
  simp only [ktD, kOf, show ¬ k < 20 by omega, h2, ↓reduceIte]

/-! ### The softmax region -/

theorem sm_find : ∀ s ∈ smSites, syAt s.pc 0 = true →
    smSites.find? (fun s' => s'.pc == s.pc) = some s ∧ 574 ≤ s.pc ∧ s.pc < 2603 := by
  decide +kernel

theorem ktD_sm {pc a i b : Nat} (h1 : 574 ≤ pc) (h2 : pc < 2603) :
    ktD (pc, a, i, b) = smTimeAt pc i := by
  simp only [ktD, show ¬ pc < 20 by omega, show ¬ pc < 574 by omega, h2, ↓reduceIte]

theorem ktD_ep {pc a i b : Nat} (h1 : 2603 ≤ pc) : ktD (pc, a, i, b) = epTimeAt pc := by
  simp only [ktD, show ¬ pc < 20 by omega, show ¬ pc < 574 by omega, show ¬ pc < 2603 by omega,
    ↓reduceIte]

/-- A softmax loop site that is not synchronizing, with its key in the region: the key's site is
later in the iteration. -/
def smLtOk (s : Sm.Site) : Bool :=
  let k := keyPc s.pc 0
  decide (574 ≤ k) && decide (k < 2603) &&
    match smSites.find? (fun s' => s'.pc == k) with
    | some s' => decide (Bound.Sm.pos s' < Bound.Sm.pos s) && decide (Bound.Sm.pos s ≤ 90) &&
        !(decide (s' = .setMaxReg) || decide (s' = .bar0))
    | none => false

theorem sm_nxt_ok : ∀ j : Fin 64, smLtOk (.nxt j) = true := by decide +kernel

theorem sm_exit_keys : 2603 ≤ keyPc Epi.Site.bar1.pc 0 ∧ 2603 ≤ keyPc Epi.Site.shfl.pc 0 ∧
    epTimeAt (keyPc Epi.Site.bar1.pc 0) = epTS .bar1 ∧
    epTimeAt (keyPc Epi.Site.shfl.pc 0) = epTS .shfl ∧
    keyPc Sm.Site.shfl4.pc 0 = Sm.Site.shfl4.pc ∧ 574 ≤ Sm.Site.shfl4.pc ∧
    Sm.Site.shfl4.pc < 2603 ∧ smTimeAt Sm.Site.shfl4.pc 0 = smTS .shfl4 0 := by
  decide +kernel

theorem smTimeAt_shfl4 (i : Nat) : smTimeAt Sm.Site.shfl4.pc i = smTS .shfl4 i := by
  unfold smTimeAt
  have : smSites.find? (fun s' => s'.pc == Sm.Site.shfl4.pc) = some .shfl4 := by decide +kernel
  rw [this]

/-! ### The epilogue -/

/-- An epilogue site that is not synchronizing and has a synchronizing site after it: that
site is later. -/
def epLtOk (s : Epi.Site) : Bool :=
  let k := keyPc s.pc 0
  !syPc k || (decide (2603 ≤ k) &&
    match epSites.find? (fun s' => s'.pc == k) with
    | some s' => decide (Bound.Epi.siteRank s' < Bound.Epi.siteRank s)
    | none => false)

theorem ep_stO_ok : ∀ k : Fin 64, epLtOk (.stO k) = true := by decide +kernel

theorem ep_find : ∀ s ∈ epSites, syAt s.pc 0 = true →
    epSites.find? (fun s' => s'.pc == s.pc) = some s ∧ 2603 ≤ s.pc := by
  decide +kernel

/-! ### The softmax cases -/

theorem smTS_loop {s : Sm.Site} (i : Nat) (h1 : s ≠ .setMaxReg) (h2 : s ≠ .bar0)
    (h3 : ∀ j, s ≠ .pre j) : smTS s i = slot i + bandS + (90 - Bound.Sm.pos s) := by
  cases s <;> simp_all [smTS]

theorem smTimeAt_of {k i : Nat} {s' : Sm.Site}
    (hf : smSites.find? (fun s => s.pc == k) = some s') : smTimeAt k i = smTS s' i := by
  unfold smTimeAt
  rw [hf]

theorem sm_lt_generic {s : Sm.Site} {a i b : Nat} (hs : smLtOk s = true) (h1 : s ≠ .setMaxReg)
    (h2 : s ≠ .bar0) (h3 : ∀ j, s ≠ .pre j) :
    smTS s i < ktD (keyPc s.pc 0, a, i, b) := by
  simp only [smLtOk, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨hk1, hk2⟩, hm⟩ := hs
  rw [ktD_sm hk1 hk2]
  split at hm
  · rename_i s' hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff]
      at hm
    obtain ⟨⟨hp, hp90⟩, hn1, hn2⟩ := hm
    have hn3 : ∀ j, s' ≠ .pre j := by
      intro j hj
      subst hj
      have := List.mem_of_find?_eq_some hf
      simp [smSites] at this
    rw [smTimeAt_of hf, smTS_loop i h1 h2 h3, smTS_loop i (by simpa using hn1)
      (by simpa using hn2) hn3]
    omega
  · exact absurd hm (by simp)

theorem epTS_lt_exit {d : Sm.D} (hI : Sm.Inv L g d) (b : Bool) :
    smTS d.site d.i < epTS (if b then .bar1 else .shfl) := by
  have := smT_lt_epi0 hI
  rw [smT_eq] at this
  cases b <;> simp only [epTS, Bound.Epi.siteRank, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem ktD_exitKey (L : Launch) (g r25 : Nat) :
    ktD (exitKey L g r25) = epTS (if skipOf r25 then .bar1 else .shfl) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := sm_exit_keys
  unfold exitKey
  cases skipOf r25 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [ktD_ep h2, h4]
  · rw [ktD_ep h1, h3]

theorem sm_lt {L : Launch} {g : Nat} {d : Sm.D} (h : smSy d = false) (hI : Sm.Inv L g d) :
    smT d < ktD (smKey L g d) := by
  have hex := epTS_lt_exit hI
  rw [smT_eq]
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only [smSy] at h
  simp only at hex ⊢
  obtain ⟨-, -, -, -, -, hk4, hk5, -⟩ := sm_exit_keys
  cases s with
  | pre j =>
    simp only [smKey, smKeyOf]
    split
    · rw [ktD_exitKey]; exact hex _
    · rw [ktD_sm (by rw [syAt_key (by decide +kernel)]; exact hk4)
        (by rw [syAt_key (by decide +kernel)]; exact hk5),
        syAt_key (by decide +kernel), smTimeAt_shfl4]
      have := pre_lt_slot i
      simp only [smTS, Bound.Sm.pos]
      have := j.isLt
      omega
  | arrive =>
    simp only [smKey, smKeyOf]
    split
    · rw [ktD_exitKey]; exact hex _
    · rw [ktD_sm (by rw [syAt_key (by decide +kernel)]; exact hk4)
        (by rw [syAt_key (by decide +kernel)]; exact hk5),
        syAt_key (by decide +kernel), smTimeAt_shfl4]
      simp only [smTS, Bound.Sm.pos]
      wt_omega
  | nxt j =>
    exact sm_lt_generic (sm_nxt_ok j) (by simp) (by simp) (by simp)
  | _ =>
    first
    | (exfalso; revert h; decide +kernel)
    | exact sm_lt_generic (by decide +kernel) (by simp) (by simp) (by simp)

/-! ### The epilogue -/

theorem ep_lt {d : Epi.D} (h : epSy d = false) (hk : syPc (epKey d).1 = true) :
    epiT d < ktD (epKey d) := by
  obtain ⟨s, pr, o, sk⟩ := d
  simp only [epSy] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := sm_exit_keys
  have hsr := Bound.Epi.siteRank_le s
  simp only [Bound.Epi.top] at hsr
  by_cases hw : s = .wait
  · subst hw
    simp only [epKey, epK, ↓reduceIte]
    cases sk <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [ktD_ep h2, h4]; simp only [epiT, epTS, Bound.Epi.siteRank]; omega
    · rw [ktD_ep h1, h3]; simp only [epiT, epTS, Bound.Epi.siteRank]; omega
  · have hok : epLtOk s = true := by
      cases s with
      | stO k => exact ep_stO_ok k
      | _ => first | (exfalso; revert h; decide +kernel) | decide +kernel
    simp only [epKey, epK, hw, ↓reduceIte] at hk ⊢
    simp only [epLtOk, hk, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    obtain ⟨hr, hm⟩ := hok
    rw [ktD_ep hr]
    split at hm
    · rename_i s' hf
      simp only [decide_eq_true_eq] at hm
      unfold epTimeAt
      rw [hf]
      simp only [epiT, epTS]
      omega
    · exact absurd hm (by simp)

/-! ### The default partition -/

/-- **A synchronizing default-partition state's key time is its time.** -/
theorem kxD_sy (L : Launch) (g : Nat) {s : DComp.St} (h : dSy s = true) :
    kxD L g s = dcompT s := by
  cases s with
  | dstart d =>
    obtain ⟨site, tm⟩ := d
    simp only [dSy, dsSy, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ds_sy_time site h.1 h.2
  | pro d =>
    have hk := pro_sy_key L g h
    replace h : syAt d.site.pc d.site.sub = true := h
    have := pro_sy_nat d.site.ctorIdx (ctorIdx_lt _) (by rw [ofNat_ctorIdx]; exact h)
    rw [ofNat_ctorIdx] at this
    obtain ⟨h1, h2, h3⟩ := this
    show ktD (kOf (proKey L g d)) = 100 + d.site.ctorIdx
    rw [hk, ktD_pro h1 h2, h3]
  | sm d =>
    have hk := sm_sy_key L g h
    have hm := mem_smSites h
    obtain ⟨hf, h1, h2⟩ := sm_find _ hm h
    show ktD (smKey L g d) = smT d
    obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
    replace h : syAt s.pc 0 = true := h
    simp only at hk hf h1 h2 hm
    have hkey : smKey L g ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ =
        (s.pc, e0.r26, i, e0.r25) := by
      cases s with
      | pre j => exact absurd h (by simp [pre_notSy j])
      | arrive => exact absurd h (by decide +kernel)
      | _ => simp only [smKey, smKeyOf, syAt_key h]
    rw [hkey, ktD_sm h1 h2, smTimeAt_of hf, smT_eq]
  | epi d =>
    have hk := ep_sy_key h
    obtain ⟨hf, h1⟩ := ep_find _ (mem_epSites h) h
    show ktD (epKey d) = epiT d
    have he : epKey d = (d.site.pc, (epKey d).2) := by rw [← hk]
    rw [he]
    obtain ⟨a, b, c⟩ := (epKey d).2
    rw [ktD_ep h1]
    unfold epTimeAt
    rw [hf]
    rfl

/-- **A default-partition state that is not synchronizing is timed below its key time**, when
the key is a synchronizing position. -/
theorem kxD_lt {L : Launch} {g : Nat} {Q : Params} {s : DComp.St} (h : dSy s = false)
    (hI : DComp.Inv L g Q s) (hk : syPc (dKey L g s).1 = true) : dcompT s < kxD L g s := by
  cases s with
  | dstart d =>
    obtain ⟨site, tm⟩ := d
    simp only [dSy, dsSy, Bool.and_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not]
      at h
    have hne : site ≠ .toProA := hI.2
    have h' : syAt site.pc site.sub = false := by
      rcases h with h | h
      · exact h
      · exact absurd h hne
    exact ds_lt_time site h' hne hk
  | pro d =>
    show 100 + d.site.ctorIdx < ktD (kOf (proKey L g d))
    obtain ⟨⟨q1, q2, q3, q4⟩, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := pro_branch_keys
    by_cases h03 : d.site = .ptc0_3
    · have hp : proKey L g d = if ProA.v_p63 L g d.dt then keyQ else siteKey .pbA1 := by
        simp only [proKey, h03]
      rw [hp, h03]
      split
      · rw [ktD_pro q1 q2]; omega
      · rw [ktD_pro a1 a2]; omega
    by_cases h13 : d.site = .ptc1_3
    · have hp : proKey L g d = if ProA.v_p72 L g d.dt then keyQ else siteKey .pbA2 := by
        simp only [proKey, h13]
      rw [hp, h13]
      split
      · rw [ktD_pro q1 q2]; omega
      · rw [ktD_pro b1 b2]; omega
    have hp : proKey L g d = siteKey d.site := by
      unfold proKey
      split <;> simp_all
    simp only [dKey, kOf] at hk
    rw [hp] at hk ⊢
    simp only [dSy, proSy] at h
    have := pro_lt_nat d.site.ctorIdx (ctorIdx_lt _) (by rw [ofNat_ctorIdx]; exact h)
    simp only [proLtOk, ofNat_ctorIdx, hk, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at this
    obtain ⟨⟨r1, r2⟩, r3⟩ := this
    rw [ktD_pro r1 r2]
    omega
  | sm d => exact sm_lt h hI
  | epi d => exact ep_lt h hk

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
