-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollShapeOp

@[expose] public section

/-! # The position of a warp collective from its time

A state's time (`stateTime`, the site tables of `Thread/Roles.lean`) determines the position of
the warp collective at the state, so the position is a function of the time (`collPc`):

* a fixed time (below `base`) is the prologue's (its shuffles and elections) or the MMA warp's
  broadcast of the Q descriptor (`shflQT`), each at a time of its own (`fixedTab`);
* a slot time `base + span (i (n + 1) + s) + o` with `o < span` and `s ≤ n` gives back the
  offset `o` and the slot `s` (`slotKey_at`); the slot's class (`slotCls`: the item's head slot
  `0`, a trip's slot, the last slot `n`) and the offset name one warp-collective site of one role
  (`slotTab`): the loader's broadcast and elections (in its use's band), the MMA warp's
  broadcasts and elections (by their part of the item), the softmax tiles' warp barriers and
  elections (by stage and tile), the correction's ballots (by stage).

`state_pc` states it for every warp-collective state of a thread with the machine's invariant:
its position is `collPc (Work.n L) (stateTime L g d)`. The tables are checked by `decide`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

/-- The value a table gives a key (`0` for none). -/
def tabGet {α : Type} [BEq α] (tab : List (α × Nat)) (k : α) : Nat :=
  ((tab.find? (·.1 == k)).map (·.2)).getD 0

/-- The prologue's warp-collective sites. -/
def proWarp : List Prologue.Site :=
  [.shfl0, .shfl1, .shfl2, .elect12, .shfl3] ++ (List.finRange 14).map .elect

/-- The warp collectives at fixed times: the prologue's and the Q descriptor's broadcast. -/
def fixedTab : List (Nat × Nat) :=
  proWarp.map (fun s => (prologue s, s.pc)) ++ [(shflQT, Mma.Site.shflQ.pc)]

/-- The class of slot `s` of an item of `n` slots after the head: the head `0`, a trip `1`, the
last `2`. -/
def slotCls (n s : Nat) : Nat := if s = 0 then 0 else if s = n then 2 else 1

/-- The slot's class and the offset of a slot time. -/
def slotKey (n τ : Nat) : Nat × Nat := (slotCls n ((τ - base) / span % (n + 1)), (τ - base) % span)

/-- The class of a loader use's slot: the head's uses `0`, a trip's `1`. -/
def useCls : Loader.UseK → Nat
  | .k | .v => 1
  | _ => 0

/-- The loader's warp collectives: the broadcast, each use's elections, the tail's election. -/
def loaderTab : List ((Nat × Nat) × Nat) :=
  [((0, 0), Loader.Site.head.pc), ((0, 14), Loader.Site.elTail.pc)] ++
    [Loader.UseK.k0, .q0, .q1, .v0, .k, .v].flatMap fun u =>
      [((useCls u, 16 * loaderBand u + 2), (Loader.Site.elA u).pc),
        ((useCls u, 16 * loaderBand u + 4), (Loader.Site.elC u 0).pc),
        ((useCls u, 16 * loaderBand u + 6), (Loader.Site.elC u 1).pc)]

/-- The MMA warp's warp collectives in its item's parts. -/
def mmaWarp : List Mma.Site :=
  (List.finRange 14).map .shfl ++ (List.finRange 8).map .elM ++ (List.finRange 12).map .elC

def mmaTab : List ((Nat × Nat) × Nat) :=
  mmaWarp.map fun s => ((Mma.region s - 1, bandM + mmaOff s), s.pc)

/-- The softmax tiles' warp barriers and elections, of both stages. -/
def softTab : List ((Nat × Nat) × Nat) :=
  [false, true].flatMap fun lp => [0, 1].flatMap fun st =>
    [(((if lp then 1 else 0), bandS st + 38), (Softmax.Site.warpBar lp).pc),
      (((if lp then 1 else 0), bandS st + 40), (Softmax.Site.el lp).pc)]

/-- The correction's ballots, of both stages. -/
def corrTab : List ((Nat × Nat) × Nat) :=
  [(0 : Fin 2), 1].map fun st => ((1, bandC st.val + 4), (Correction.Site.vote st).pc)

def slotTab : List ((Nat × Nat) × Nat) := loaderTab ++ mmaTab ++ softTab ++ corrTab

/-- **The position of the warp collective at a time.** -/
def collPc (n τ : Nat) : Nat :=
  if τ < base then tabGet fixedTab τ else tabGet slotTab (slotKey n τ)

/-! ### Decoding a time -/

theorem slotKey_at {n i s o : Nat} (hs : s ≤ n) (ho : o < span) :
    slotKey n (slotTime n i s o) = (slotCls n s, o) := by
  have h : slotTime n i s o - base = o + span * (i * (n + 1) + s) := by
    unfold slotTime gslot; omega
  simp only [slotKey, h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho,
    Nat.add_mul_div_left _ _ (show 0 < span by decide), Nat.div_eq_of_lt ho, Nat.zero_add,
    Nat.add_comm (i * (n + 1)) s, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hs)]

theorem collPc_slot {n i s o : Nat} (hs : s ≤ n) (ho : o < span) :
    collPc n (slotTime n i s o) = tabGet slotTab (slotCls n s, o) := by
  have : ¬ slotTime n i s o < base := Nat.not_lt.mpr Progress.Time.base_le
  simp only [collPc, this, ↓reduceIte, slotKey_at hs ho]

theorem slotCls_zero (n : Nat) : slotCls n 0 = 0 := rfl

theorem slotCls_trip {n t : Nat} (h : t + 1 < n) : slotCls n (t + 1) = 1 := by
  simp only [slotCls]; split_ifs <;> omega

theorem slotCls_last {n : Nat} (h : 0 < n) : slotCls n n = 2 := by
  simp only [slotCls]; split_ifs <;> omega

/-! ### The roles' warp-collective sites -/

theorem pro_pc (n : Nat) {s : Prologue.Site} (hk : prologueKind s = .warp) :
    collPc n (prologue s) = s.pc := by
  have hl := Progress.Time.prologue_lt_reg s
  have : prologue s < base := by simp only [regT, base] at hl ⊢; omega
  simp only [collPc, this, ↓reduceIte]
  have he : ∀ e : Fin 14, tabGet fixedTab (prologue (.elect e)) = (Prologue.Site.elect e).pc := by
    decide +kernel
  cases s <;> simp only [prologueKind, reduceCtorEq] at hk
  all_goals first | exact he _ | decide +kernel

theorem mma_tab : ∀ s ∈ mmaWarp,
    tabGet slotTab (Mma.region s - 1, bandM + mmaOff s) = s.pc ∧
      (Mma.region s = 1 ∨ Mma.region s = 2 ∨ Mma.region s = 3) ∧ bandM + mmaOff s < span := by
  decide +kernel

theorem loader_tab : ∀ u : Loader.UseK,
    tabGet slotTab (useCls u, 16 * loaderBand u + 2) = (Loader.Site.elA u).pc ∧
    tabGet slotTab (useCls u, 16 * loaderBand u + 4) = (Loader.Site.elC u 0).pc ∧
    tabGet slotTab (useCls u, 16 * loaderBand u + 6) = (Loader.Site.elC u 1).pc := by
  intro u; cases u <;> decide +kernel

theorem soft_tab : ∀ (lp : Bool) (st : Fin 2),
    tabGet slotTab ((if lp then 1 else 0), bandS st.val + 38) = (Softmax.Site.warpBar lp).pc ∧
    tabGet slotTab ((if lp then 1 else 0), bandS st.val + 40) = (Softmax.Site.el lp).pc := by
  decide +kernel

theorem corr_tab : ∀ st : Fin 2,
    tabGet slotTab (1, bandC st.val + 4) = (Correction.Site.vote st).pc := by
  decide +kernel

/-- The loader's warp collectives. -/
theorem loader_pc {n T : Nat} {d : Loader.D} (hk : loaderKind d.site = .warp)
    (htrip : d.site.inTrip = true → d.t + 2 ≤ n) :
    collPc n (Progress.Time.loader n T d) = d.site.pc := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  have hslot : ∀ u : Loader.UseK, (u = .k ∨ u = .v → t + 2 ≤ n) →
      loaderSlot t u ≤ n ∧ slotCls n (loaderSlot t u) = useCls u := by
    intro u hu
    cases u <;> simp only [loaderSlot, useCls, slotCls_zero, Nat.zero_le, and_self,
      reduceCtorEq, or_false, false_or, forall_const] at hu ⊢
    all_goals exact ⟨by omega, slotCls_trip (by omega)⟩
  have hb : ∀ u, loaderBand u ≤ 3 := fun u => by cases u <;> decide
  cases site <;> simp only [loaderKind, reduceCtorEq] at hk
  · simp only [Progress.Time.loader, loaderUse, bandL]
    rw [collPc_slot (Nat.zero_le _) (by decide), slotCls_zero]
    decide +kernel
  · rename_i u
    obtain ⟨h1, h2⟩ := hslot u (by
      rintro (rfl | rfl) <;> exact htrip (by simp [Loader.Site.inTrip]))
    simp only [Progress.Time.loader, loaderUse, bandL, Nat.zero_add]
    rw [collPc_slot h1 (by have := hb u; simp only [span]; omega), h2]
    exact (loader_tab u).1
  · rename_i u j
    obtain ⟨h1, h2⟩ := hslot u (by
      rintro (rfl | rfl) <;> exact htrip (by simp [Loader.Site.inTrip]))
    simp only [Progress.Time.loader, loaderUse, bandL, Nat.zero_add]
    rw [collPc_slot h1 (by have := hb u; have := j.isLt; simp only [span]; omega), h2]
    fin_cases j
    · exact (loader_tab u).2.1
    · exact (loader_tab u).2.2
  · simp only [Progress.Time.loader, tailTime]
    rw [collPc_slot (Nat.zero_le _) (by decide), slotCls_zero]
    decide +kernel

/-- The MMA warp's warp collectives. -/
theorem mma_pc {n T : Nat} {d : Mma.D} (hk : mmaKind d.site = .warp)
    (h2 : Mma.region d.site = 2 → d.t + 1 < n) (h3 : Mma.region d.site = 3 → d.t + 1 = n) :
    collPc n (Progress.Time.mma n T d) = d.site.pc := by
  obtain ⟨site, i, t, b, pro⟩ := d
  simp only at h2 h3 ⊢
  by_cases hq : site = .shflQ
  · subst hq
    have : shflQT < base := by decide
    simp only [Progress.Time.mma, collPc, this, ↓reduceIte]
    decide +kernel
  have hmem : site ∈ mmaWarp := by
    cases site <;> simp only [mmaKind, reduceCtorEq] at hk
    · exact absurd rfl hq
    all_goals simp [mmaWarp]
  obtain ⟨htab, hr, hoff⟩ := mma_tab site hmem
  have ht : Progress.Time.mma n T ⟨site, i, t, b, pro⟩ = mmaAt n i
      (if Mma.region site = 1 then 0 else if Mma.region site = 2 then t + 1 else n)
      (mmaOff site) := by
    cases site <;> simp only [mmaKind, reduceCtorEq] at hk
    · exact absurd rfl hq
    all_goals simp only [Progress.Time.mma]
    all_goals split_ifs <;> rfl
  rw [ht, mmaAt, ← htab]
  rcases hr with hr | hr | hr
  · simp only [hr, ↓reduceIte]
    rw [collPc_slot (Nat.zero_le _) hoff, slotCls_zero]
  · have := h2 hr
    have e : (if Mma.region site = 1 then 0 else if Mma.region site = 2 then t + 1 else n) =
        t + 1 := by simp [hr]
    rw [e, hr, collPc_slot (by omega) hoff, slotCls_trip this]
  · have := h3 hr
    have e : (if Mma.region site = 1 then 0 else if Mma.region site = 2 then t + 1 else n) =
        n := by simp [hr]
    rw [e, hr, collPc_slot le_rfl hoff, slotCls_last (by omega)]

/-- The softmax tiles' warp collectives. -/
theorem soft_pc {n T st : Nat} {d : Softmax.D} (hst : st < 2) (hk : softmaxKind d.site = .warp)
    (htrip : d.site.inTrip = true → d.t + 1 < n) :
    collPc n (Progress.Time.softmax n T st d) = d.site.pc := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  simp only at htrip ⊢
  have hs : ∀ lp : Bool, (lp = true → t + 1 < n) →
      softSlot ⟨site, i, t, w, m, l⟩ lp ≤ n ∧
        slotCls n (softSlot ⟨site, i, t, w, m, l⟩ lp) = if lp then 1 else 0 := by
    intro lp h
    cases lp
    · simp [softSlot, slotCls_zero]
    · have := h rfl
      simp only [softSlot, ↓reduceIte]
      exact ⟨by omega, slotCls_trip this⟩
  have hst' : st = (⟨st, hst⟩ : Fin 2).val := rfl
  cases site <;> simp only [softmaxKind, reduceCtorEq] at hk
  all_goals rename_i lp
  all_goals obtain ⟨h1, h2⟩ := hs lp (fun h => htrip (by subst h; rfl))
  all_goals simp only [Progress.Time.softmax]
  all_goals rw [collPc_slot h1 (by simp only [bandS, span]; omega), h2, hst']
  · exact (soft_tab lp _).1
  · exact (soft_tab lp _).2

/-- The correction's ballots. -/
theorem corr_pc {n T : Nat} {d : Correction.D} (hk : corrKind d.site = .warp)
    (htrip : d.site.inTrip = true → d.t + 1 < n) :
    collPc n (Progress.Time.correction n T d) = d.site.pc := by
  cases hs : d.site <;> simp only [hs, corrKind, reduceCtorEq] at hk
  rename_i st
  have h := htrip (by rw [hs]; rfl)
  simp only [Progress.Time.correction, hs]
  rw [collPc_slot (by omega) (by simp only [bandC, span]; omega), slotCls_trip h]
  exact corr_tab st

/-- **The position of a thread's warp-collective state is the position of its time.** -/
theorem state_pc {L : Launch} {g : Nat} {d : ThreadD} (hinv : (code L g).inv d)
    (hk : nextKind d = .warp) : (code L g).pc d = collPc (Work.n L) (stateTime L g d) := by
  rcases d with ⟨s⟩ | (s | l | m | s | s | c)
  · exact (pro_pc _ hk).symm
  · obtain ⟨site⟩ := s
    cases site <;> simp [nextKind, idleKind] at hk
  · have hi : Loader.Inv L g l := hinv
    exact (loader_pc hk hi.trip).symm
  · have hi : Mma.Inv L g m := hinv.1
    have htr := hi.trip
    unfold Mma.TripOk at htr
    refine (mma_pc hk (fun h => ?_) (fun h => ?_)).symm
    · rw [h] at htr; exact htr
    · rw [h] at htr; exact htr
  · cases hs : s.site <;> simp [nextKind, storeKind, hs] at hk
  · have hi : Softmax.Inv L g s := hinv
    have hst : Softmax.stOf L g < 2 := by
      have := hi.warp; simp only [Softmax.stOf]; omega
    exact (soft_pc hst hk hi.trip).symm
  · have hi : Correction.Inv L g c := hinv
    exact (corr_pc hk hi.trip).symm

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
