-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpBase

@[expose] public section

/-! # A lane waiting at a warp collective is past the first state (`Cross.WarpLagPos`)

Only the machine's first state, the prologue's first shuffle, has time 0: every other prologue
site is later, every role site is at a fixed time from `setmaxnreg` on or in a slot
(`stateTime_pos`). No step returns to the first state (`next_ne_init`), so a thread there has an
empty trace and has made no warp collective. A lane of its warp with no more of them that is not
at a warp collective has no event either (its first event, from the first state, is the first
shuffle) and is then at the first state, a warp collective. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every state but the first has a positive time. -/
theorem stateTime_pos {g : Nat} (d : ThreadD) (hd : d ≠ .inl ⟨.shfl0⟩) : 0 < stateTime L g d := by
  have hb : ∀ x, 0 < base + x := fun x => by simp only [base]; omega
  have hb2 : ∀ x y, 0 < base + x + y := fun x y => by simp only [base]; omega
  rcases d with p | r
  · obtain ⟨s⟩ := p
    cases s <;> simp_all [stateTime, prologue, clArriveT, clWaitT]
  · cases r with
    | idle s => obtain ⟨site⟩ := s; cases site <;> simp [stateTime, idle, regT, idleExitT]
    | loader l =>
      obtain ⟨s, i, t, a, b, c⟩ := l
      cases s <;> simp only [stateTime, loader, loaderUse, slotTime, tailTime, regT] <;>
        first | decide | exact hb _ | exact hb2 _ _
    | mma m =>
      obtain ⟨s, i, t, b, pro⟩ := m
      cases s <;> simp only [stateTime, mma, mmaAt, mmaTail, slotTime, tailTime, regT, allocT,
        allocWriteT, bar0T, ldBaseT, shflQT] <;> (try split_ifs) <;>
        first | decide | exact hb2 _ _
    | store s =>
      obtain ⟨s, i⟩ := s
      cases s <;> simp only [stateTime, store, storeAt, slotTime, tailTime, regT] <;>
        first | decide | exact hb2 _ _
    | softmax sd =>
      obtain ⟨s, i, t, w, m, l⟩ := sd
      cases s <;> simp only [stateTime, softmax, slotTime, tailTime, regT, bar0T] <;>
        (try split) <;> first | decide | exact hb2 _ _
    | corr cd =>
      obtain ⟨s, i, t, aw, a, o⟩ := cd
      cases s <;>
        simp only [stateTime, correction, slotTime, tailTime, regT, bar0T, freeT, base] <;>
        (try split) <;> omega

/-- No step of a thread's machine returns to its first state. -/
theorem next_ne_init {g : Nat} (d : ThreadD) (e : Event) :
    (code L g).next d e ≠ some (some (.inl ⟨.shfl0⟩)) := by
  intro h
  rcases d with p | r
  · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = _ at h
    cases hx : Prologue.next L g p e with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      rcases x with _ | ⟨p' | k⟩
      · cases h
      · simp only [Option.map_some, Option.bind_some, handoff, Option.some.injEq,
          Sum.inl.injEq] at h
        subst h
        obtain ⟨s⟩ := p
        have hag : ∀ k : Fin 14, Prologue.afterGroup k ≠ .shfl0 := by decide
        have hin : ∀ j : Fin 36, Prologue.initNext j ≠ .shfl0 := by decide
        cases s <;> simp only [Prologue.next] at hx
        all_goals (repeat' split at hx)
        all_goals simp_all
      · simp only [Option.map_some, Option.bind_some, handoff] at h
        cases hs : Role.start L g k <;> rw [hs] at h <;> simp at h
  · obtain ⟨r', h', -⟩ := code_next_inr h
    cases h'

/-- A thread at its first state, before an event or at the trace's end, has made none. -/
theorem init_zero {g k : Nat} (hk : k ≤ (X.tr g).length)
    (hσ : St L X g k = some (some (.inl ⟨.shfl0⟩))) : k = 0 := by
  cases k with
  | zero => rfl
  | succ j =>
    exfalso
    have hj : j < (X.tr g).length := by omega
    have he : (X.tr g)[j]? = some (X.tr g)[j] := List.getElem?_eq_getElem hj
    unfold St at hσ
    rw [Frame.stateAt_succ he] at hσ
    cases hs : Frame.stateAt (code L) X g j with
    | none => rw [hs] at hσ; cases hσ
    | some σ =>
      rw [hs] at hσ
      cases σ with
      | none => cases hσ
      | some d => exact next_ne_init d _ hσ

/-- **`Cross.WarpLagPos`.** -/
theorem warpLagPos (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hok : SitesTmplOk L) : WarpLagPos L X := by
  intro g h d hg hh hw hσ hk hc hn
  by_contra h0
  have hd : d = .inl ⟨.shfl0⟩ := by
    by_contra hne
    exact h0 (stateTime_pos d hne)
  subst hd
  have hl := init_zero le_rfl hσ
  have hcg : (X.tr g).countP Sched.isWarpColl = 0 := by
    rw [List.length_eq_zero_iff.mp hl]; rfl
  rw [hcg] at hc hn
  have hch : (X.tr h).countP Sched.isWarpColl = 0 := by omega
  rcases Nat.eq_zero_or_pos (X.tr h).length with hlh | hlh
  · apply hn
    refine ⟨hch, (code L h).init, ?_, rfl⟩
    rw [hlh]
    exact Frame.stateAt_zero
  · have he : X.get (h, 0) = some (X.tr h)[0] := List.getElem?_eq_getElem hlh
    have hσ0 : St L X h 0 = some (some (code L h).init) := Frame.stateAt_zero
    have hwc := (fired_kind hpre hX hok hh hσ0 he).1
    have h1 : 0 < (X.tr h).countP Sched.isWarpColl := by
      refine List.countP_pos_iff.mpr ⟨(X.tr h)[0], List.getElem_mem hlh, ?_⟩
      rw [hwc]; rfl
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
