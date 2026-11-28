-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Bar12Role
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime

@[expose] public section

/-! # The phase of a state relative to barrier 12

The phase of a state (`ph`): `1` at a role's closing `barrier.sync 12` (the MMA and TMA lanes'
`outBar`, the index warp's and warpgroup 2's `bar`, the idle code's `bar`), `2` after it (the
exit, the idle code's `ret`), `0` elsewhere (the startup, warpgroup 1's head, warpgroup 0). For a
lane of warps 4–11 a state of phase `0` is before `endSlot`, of phase `1` at it, of phase `2`
after it (`ph_time`); a state firing a barrier-12 event is of phase `1`, one firing an `exit` of
phase `2`, and a state of phase `1` fires barrier 12 (`ph_ev`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The phase -/

/-- The phase of a sub-role's state. -/
def subPh (P : Params) (L : Launch) (g : Nat) : (j : SubEntry) → (subFrag P L g j).D → Nat
  | .mma => fun d => mmaPh d.site
  | .tma => fun d => tmaPh d.site
  | .index => fun d => ixPh d.site
  | .idle => fun s => idlePh s

/-- The phase of a state of warpgroup 1. -/
def wg1Ph (P : Params) (L : Launch) (g : Nat) : (wg1Code P L g).D → Nat
  | .inr ⟨.inl j, d⟩ => subPh P L g j d
  | _ => 0

/-- The phase of a warpgroup's state. -/
def fragPh (P : Params) (L : Launch) (g : Nat) : (i : Entry) → (frag P L g i).D → Nat
  | .wg0 => fun _ => 0
  | .wg1 => wg1Ph P L g
  | .dequant => fun d => deqPh d.site

/-- **The phase of a state** relative to barrier 12. -/
def ph (P : Params) (L : Launch) (g : Nat) : (thread P L g).D → Nat
  | (.inr ⟨.inl i, d⟩, _) => fragPh P L g i d
  | _ => 0

/-! ### No undefined behaviour in the counts -/

theorem mma_ubCls : ∀ f, Mma.cls .ub f = true → ∃ fl, f.kind = .ub fl := fun f h => by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨fl, rfl⟩
  | wait l q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at h
  | tc t => cases t <;> simp [Mma.cls, Mma.kindOf] at h
  | _ => simp [Mma.cls, Mma.kindOf] at h

theorem tma_ubCls : ∀ f, Tma.cls .ub f = true → ∃ fl, f.kind = .ub fl := fun f h => by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨fl, rfl⟩
  | wait l q ok a sc => cases ok <;> simp [Tma.cls, Tma.kindOf] at h
  | _ => simp [Tma.cls, Tma.kindOf] at h

theorem ix_ubCls : ∀ f, Index.cls .ub f = true → ∃ fl, f.kind = .ub fl := fun f h => by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨fl, rfl⟩
  | wait l q ok a sc => cases ok <;> simp [Index.cls, Index.kindOf] at h
  | _ => simp [Index.cls, Index.kindOf] at h

theorem deq_ubCls : ∀ f, Dequant.cls .ub f = true → ∃ fl, f.kind = .ub fl := fun f h => by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨fl, rfl⟩
  | wait l q ok a sc => cases ok <;> simp [Dequant.cls, Dequant.kindOf] at h
  | _ => simp [Dequant.cls, Dequant.kindOf] at h

theorem cls_ubCls : ∀ f, cls .ub f = true → ∃ fl, f.kind = .ub fl := fun f h => by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨fl, rfl⟩
  | _ => simp [cls] at h

/-- A count of undefined behaviour of a state is `0`. -/
theorem ph_ubZero (hnu : ¬ HasUb X) {i : Nat} {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) {c : Cls}
    (hc : ∀ f, cls c f = true → ∃ fl, f.kind = .ub fl) : σ.2 c = 0 :=
  (state_count hσ c).trans (w0_noUbTakeW_pre hc (noUbBefore_of_noUb hnu))

/-! ### The phase and the time -/

theorem wg0_warp (hg : wgOf L g = 0) : warp L g < 4 := by
  simp only [wgOf, tidOf] at hg
  simp only [warp]
  omega

/-- **The time of a state by its phase**, for a lane of warps 4–11. -/
theorem ph_time (hnu : ¬ HasUb X) (hw : 4 ≤ warp L g) {i : Nat} {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) (hJ : (table P L).J g σ) :
    (ph P L g σ = 0 → time P L g σ < endSlot) ∧ (ph P L g σ = 1 → time P L g σ = endSlot) ∧
      (ph P L g σ = 2 → endSlot < time P L g σ) := by
  have h0 : σ.2 .ub = 0 := ph_ubZero hnu hσ cls_ubCls
  have hE : endSlot = 140 + 128 * (67108864 + 4) := rfl
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hσ
    have := Startup.time_lt hx
    simp only [ph, time]
    omega
  · cases i with
    | wg0 =>
      obtain ⟨-, -, -, hg⟩ := hJ
      have := wg0_warp hg
      omega
    | dequant =>
      obtain ⟨-, hR, -, -⟩ := hJ
      have hu : n (.dequant .ub) = 0 := ph_ubZero hnu hσ (c := .dequant .ub) deq_ubCls
      have h := deq_phPlace (hR h0) hu
      simp only [Dequant.endPlace, deqOrg, hE] at h
      simp only [ph, fragPh, time, fragTime, dequantTime, Dequant.time, idleBase, roleBase, hE]
      omega
    | wg1 =>
      obtain ⟨-, hW, -, -⟩ := hJ
      rcases d with s | ⟨j | r, d⟩
      · have := Wg1.time_le s
        simp only [ph, fragPh, wg1Ph, time, fragTime, wg1Time, roleBase, hE]
        omega
      · cases j with
        | mma =>
          obtain ⟨-, -, ⟨hR, -⟩, -⟩ := hW
          have hu : n (.mma .ub) = 0 := ph_ubZero hnu hσ (c := .mma .ub) mma_ubCls
          have h := mma_phPlace (hR h0 hu)
          simp only [Mma.endPlace, mmaOrg, hE] at h
          simp only [ph, fragPh, wg1Ph, subPh, time, fragTime, wg1Time, mmaTime, Mma.time,
            idleBase, roleBase, hE]
          omega
        | tma =>
          obtain ⟨-, -, ⟨hR, -⟩, -⟩ := hW
          have hu : n (.tma .ub) = 0 := ph_ubZero hnu hσ (c := .tma .ub) tma_ubCls
          have h := tma_phPlace (hR h0 hu)
          simp only [Tma.endPlace, tmaOrg, hE] at h
          simp only [ph, fragPh, wg1Ph, subPh, time, fragTime, wg1Time, tmaTime, Tma.time,
            idleBase, roleBase, hE]
          omega
        | index =>
          obtain ⟨-, -, hR⟩ := hW
          have hu : n (.index .ub) = 0 := ph_ubZero hnu hσ (c := .index .ub) ix_ubCls
          have h := ix_phPlace (hR h0 hu)
          simp only [Index.ixEndPlace, ixOrg, hE] at h
          simp only [ph, fragPh, wg1Ph, subPh, time, fragTime, wg1Time, indexTime, Index.time,
            idleBase, roleBase, hE]
          omega
        | idle =>
          show (idlePh d = 0 → idleTime d < endSlot) ∧ (idlePh d = 1 → idleTime d = endSlot) ∧
            (idlePh d = 2 → endSlot < idleTime d)
          cases d <;> simp [idlePh, idleTime, Wg1.itime, idleBase, roleBase, hE]
      · exact hW.elim
  · exact hJ.elim

/-! ### The phase and the events -/

theorem start_noBar12 {d : Startup.D} {e : Event} (hx : Startup.exitOf d = none)
    (hev : Startup.Ev L g d e) {c : Option Nat} {md : BarMode} (hk : e.kind = .bar 12 c md) :
    False := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => fin_cases j <;> obtain ⟨r, ok, h⟩ := hev <;> rw [hk] at h <;> cases h
  | elect j => obtain ⟨i, l, -, h⟩ := hev; rw [hk] at h; cases h
  | ld => rcases hev with ⟨a, bs, h, -⟩ | ⟨f, h⟩ <;> rw [hk] at h <;> cases h
  | allocSt => obtain ⟨c, -, h⟩ := hev; rw [hk] at h; cases h
  | enter r => simp [Startup.exitOf] at hx
  | _ => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev

/-- **A state firing an `exit` or a barrier-12 event**, of a lane of warps 4–11, is of phase `2`
(an exit) or `1`; a state of phase `1` fires barrier 12. -/
theorem ph_ev (hw : 4 ≤ warp L g) {σ : (thread P L g).D} {e : Event} (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) :
    ((e.kind = .exit ∨ ∃ c md, e.kind = .bar 12 c md) →
      (ph P L g σ = 2 ∧ e.kind = .exit) ∨ ph P L g σ = 1) ∧
    (ph P L g σ = 1 → e.kind = .bar 12 none .sync) := by
  cases state_role hJ hi with
  | startup d n _ _ hx _ _ =>
    refine ⟨fun hk => ?_, fun h => by simp [ph] at h⟩
    rcases hk with hk | ⟨c, md, hk⟩
    · exact (start_noExit hx hev hk).elim
    · exact (start_noBar12 hx hev hk).elim
  | head s n hs _ _ _ _ =>
    refine ⟨fun hk => ?_, fun h => by simp [ph, fragPh, wg1Ph] at h⟩
    have hE : Wg1.Ev L g s e := hev
    rcases hs with rfl | rfl <;> rcases hk with hk | ⟨c, md, hk⟩ <;>
      simp [Wg1.Ev, hk] at hE
  | idle s n _ _ _ _ =>
    have hE : Wg1.IEv s e := hev
    show ((e.kind = .exit ∨ ∃ c md, e.kind = .bar 12 c md) →
      (idlePh s = 2 ∧ e.kind = .exit) ∨ idlePh s = 1) ∧ (idlePh s = 1 → _)
    cases s with
    | bar => exact ⟨fun _ => .inr rfl, fun _ => hE⟩
    | ret => exact ⟨fun _ => .inl ⟨rfl, hE⟩, fun h => by simp [idlePh] at h⟩
    | _ =>
      refine ⟨fun hk => ?_, fun h => by simp [idlePh] at h⟩
      rcases hk with hk | ⟨c, md, hk⟩ <;> rcases hE with ⟨a, bs, h⟩ | ⟨f, h⟩ <;>
        rw [hk] at h <;> cases h
  | index d n _ _ _ _ =>
    have hE : Index.Ev P L g d e := hev
    show (_ → (ixPh d.site = 2 ∧ _) ∨ ixPh d.site = 1) ∧ (ixPh d.site = 1 → _)
    refine ⟨fun hk => ?_, fun h => ?_⟩
    · rcases ix_evEnd hE hk with ⟨h1, h2⟩ | h1
      · simp [ixPh, h1, h2]
      · simp [ixPh, h1]
    · have hb : d.site = .bar := by unfold ixPh at h; split at h <;> simp_all
      have := hE.2
      simp only [Index.EvK, hb] at this
      exact this
  | mma d n _ _ hl _ _ _ =>
    have hE : Mma.Ev L g d e := hev
    show (_ → (mmaPh d.site = 2 ∧ _) ∨ mmaPh d.site = 1) ∧ (mmaPh d.site = 1 → _)
    refine ⟨fun hk => ?_, fun h => ?_⟩
    · rcases mma_evEnd hl hE hk with ⟨h1, h2⟩ | h1
      · simp [mmaPh, h1, h2]
      · simp [mmaPh, h1]
    · have hb : d.site = .outBar := by unfold mmaPh at h; split at h <;> simp_all
      have := hE.2
      simp only [Mma.EvK, hb] at this
      exact this
  | tma d n _ _ hl _ _ _ =>
    have hE : Tma.Ev L g d e := hev
    show (_ → (tmaPh d.site = 2 ∧ _) ∨ tmaPh d.site = 1) ∧ (tmaPh d.site = 1 → _)
    refine ⟨fun hk => ?_, fun h => ?_⟩
    · rcases tma_evEnd hl hE hk with ⟨h1, h2⟩ | h1
      · simp [tmaPh, h1, h2]
      · simp [tmaPh, h1]
    · have hb : d.site = .outBar := by unfold tmaPh at h; split at h <;> simp_all
      have := hE.2
      simp only [Tma.EvK, hb] at this
      exact this
  | dequant d n _ _ _ _ =>
    have hE : Dequant.Ev L g d e := hev
    show (_ → (deqPh d.site = 2 ∧ _) ∨ deqPh d.site = 1) ∧ (deqPh d.site = 1 → _)
    refine ⟨fun hk => ?_, fun h => ?_⟩
    · rcases deq_evEnd hE hk with ⟨h1, h2⟩ | h1
      · simp [deqPh, h1, h2]
      · simp [deqPh, h1]
    · have hb : d.site = .bar := by unfold deqPh at h; split at h <;> simp_all
      have := hE.2
      simp only [Dequant.EvK, hb] at this
      exact this
  | wg0 d n _ hw' _ _ => omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
