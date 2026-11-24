-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProABase
public import Kernels.InklingRelDecode.Proof.Thread.ProASeg00
public import Kernels.InklingRelDecode.Proof.Thread.ProASeg01
public import Kernels.InklingRelDecode.Proof.Thread.ProASeg02
public import Kernels.InklingRelDecode.Proof.Thread.ProASeg03
public import Kernels.InklingRelDecode.Proof.Thread.ProADiv
public import Kernels.InklingRelDecode.Proof.Thread.ProAShfl

@[expose] public section

/-! # The entry to the query loads

From pc 316 (after the preload, or at once when `num_pre` is zero) the code computes the
addresses of the 64 query loads, and each group of 16 loads is guarded by one row-validity
predicate: a group whose predicate is false is skipped by local steps. `qseg G` runs from the
checkpoint before group `G` to the first site that is a load of a valid group, else to the first
store of the packed rows (`qSite`); `qenter` runs from pc 316. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- A segment that starts with a fact the table's facts hold. -/
theorem seg_ex1 {a b n : Nat} {dt : Dat} {r : Nat} {v : Value} {G : List (Nat × Value)}
    (hp : valueOf L g dt r = v) (hl : r ∈ Flow.live a)
    (s : Seg kernel asms L g n a ((r, v) :: factsAt L g a dt) b G) :
    Seg kernel asms L g n a (factsAt L g a dt) b G :=
  s.weaken_start fun _ hR => ⟨holds_mem hR (mem_facts hl hp), hR⟩


/-- From the last checkpoint of the loads to the first store: the packing of the rows. -/
theorem qlast (L : Launch) (g : Nat) (dt : Dat) (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, Seg kernel asms L g n 515 (factsAt L g 515 dt) 526 (factsAt L g 526 dt) :=
  ⟨_, (Seg.comp (seg_515_522 L g dt) (Seg.comp (seg_522_523 L g dt hqb) (Seg.comp (seg_523_524 L g
      dt hqb) (Seg.comp (seg_524_525 L g dt hqb) (seg_525_526 L g dt hqb)))))⟩

theorem qseg3 (L : Launch) (g : Nat) (dt : Dat) (hqz : ∀ j, 48 ≤ j → dt.q j = qZero)
    (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, Seg kernel asms L g n 483 (factsAt L g 483 dt) (qSite L g dt 3).pc
      (factsAt L g (qSite L g dt 3).pc dt) := by
  by_cases hp : v_p84 L g dt = true
  · rw [show qSite L g dt 3 = .ldq48 by simp [qSite, hp]]
    exact ⟨_, seg_483_484 L g dt (fun j h1 _ => hqz j (by omega))⟩
  · have hp' : v_p84 L g dt = false := by simpa using hp
    have hv : valueOf L g dt 84 = .pred false := by
      simp [valueOf, table, PTX.Flow.lookupLit, hp']
    obtain ⟨n, hn⟩ := qlast L g dt hqb
    rw [show qSite L g dt 3 = .stq0_0 by simp [qSite, hp']]
    exact ⟨_, Seg.comp (Seg.comp (seg_ex1 (r := 84) (v := .pred false) hv (by table_decide)
        (seg_483_495_skipG L g dt (fun j h1 _ => hqz j (by omega)))) (Seg.comp (seg_ex1 (r := 84) (v
        := .pred false) hv (by table_decide) (seg_495_507_skipG L g dt (fun j h1 _ => hqz j
        (by omega)))) (seg_ex1 (r := 84) (v := .pred false) hv (by table_decide) (seg_507_515_skipG
        L g dt (fun j h1 _ => hqz j (by omega)))))) hn⟩

theorem qseg2 (L : Launch) (g : Nat) (dt : Dat) (hqz : ∀ j, 32 ≤ j → dt.q j = qZero)
    (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, Seg kernel asms L g n 451 (factsAt L g 451 dt) (qSite L g dt 2).pc
      (factsAt L g (qSite L g dt 2).pc dt) := by
  by_cases hp : v_p83 L g dt = true
  · rw [show qSite L g dt 2 = .ldq32 by simp [qSite, hp]]
    exact ⟨_, seg_451_452 L g dt (fun j h1 _ => hqz j (by omega))⟩
  · have hp' : v_p83 L g dt = false := by simpa using hp
    have hv : valueOf L g dt 83 = .pred false := by
      simp [valueOf, table, PTX.Flow.lookupLit, hp']
    obtain ⟨n, hn⟩ := qseg3 L g dt (fun j hj => hqz j (by omega)) hqb
    rw [show qSite L g dt 2 = qSite L g dt 3 by simp [qSite, hp']]
    exact ⟨_, Seg.comp (Seg.comp (seg_ex1 (r := 83) (v := .pred false) hv (by table_decide)
        (seg_451_463_skipG L g dt (fun j h1 _ => hqz j (by omega)))) (Seg.comp (seg_ex1 (r := 83) (v
        := .pred false) hv (by table_decide) (seg_463_475_skipG L g dt (fun j h1 _ => hqz j
        (by omega)))) (seg_ex1 (r := 83) (v := .pred false) hv (by table_decide) (seg_475_483_skipG
        L g dt (fun j h1 _ => hqz j (by omega)))))) hn⟩

theorem qseg1 (L : Launch) (g : Nat) (dt : Dat) (hqz : ∀ j, 16 ≤ j → dt.q j = qZero)
    (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, Seg kernel asms L g n 419 (factsAt L g 419 dt) (qSite L g dt 1).pc
      (factsAt L g (qSite L g dt 1).pc dt) := by
  by_cases hp : v_p82 L g dt = true
  · rw [show qSite L g dt 1 = .ldq16 by simp [qSite, hp]]
    exact ⟨_, seg_419_420 L g dt (fun j h1 _ => hqz j (by omega))⟩
  · have hp' : v_p82 L g dt = false := by simpa using hp
    have hv : valueOf L g dt 82 = .pred false := by
      simp [valueOf, table, PTX.Flow.lookupLit, hp']
    obtain ⟨n, hn⟩ := qseg2 L g dt (fun j hj => hqz j (by omega)) hqb
    rw [show qSite L g dt 1 = qSite L g dt 2 by simp [qSite, hp']]
    exact ⟨_, Seg.comp (Seg.comp (seg_ex1 (r := 82) (v := .pred false) hv (by table_decide)
        (seg_419_431_skipG L g dt (fun j h1 _ => hqz j (by omega)))) (Seg.comp (seg_ex1 (r := 82) (v
        := .pred false) hv (by table_decide) (seg_431_443_skipG L g dt (fun j h1 _ => hqz j
        (by omega)))) (seg_ex1 (r := 82) (v := .pred false) hv (by table_decide) (seg_443_451_skipG
        L g dt (fun j h1 _ => hqz j (by omega)))))) hn⟩

theorem qseg0 (L : Launch) (g : Nat) (dt : Dat) (hqz : ∀ j, 0 ≤ j → dt.q j = qZero)
    (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, Seg kernel asms L g n 387 (factsAt L g 387 dt) (qSite L g dt 0).pc
      (factsAt L g (qSite L g dt 0).pc dt) := by
  by_cases hp : v_p81 L g dt = true
  · rw [show qSite L g dt 0 = .ldq0 by simp [qSite, hp]]
    exact ⟨_, seg_387_388 L g dt (fun j h1 _ => hqz j (by omega))⟩
  · have hp' : v_p81 L g dt = false := by simpa using hp
    have hv : valueOf L g dt 81 = .pred false := by
      simp [valueOf, table, PTX.Flow.lookupLit, hp']
    obtain ⟨n, hn⟩ := qseg1 L g dt (fun j hj => hqz j (by omega)) hqb
    rw [show qSite L g dt 0 = qSite L g dt 1 by simp [qSite, hp']]
    exact ⟨_, Seg.comp (Seg.comp (seg_ex1 (r := 81) (v := .pred false) hv (by table_decide)
        (seg_387_399_skipG L g dt (fun j h1 _ => hqz j (by omega)))) (Seg.comp (seg_ex1 (r := 81) (v
        := .pred false) hv (by table_decide) (seg_399_411_skipG L g dt (fun j h1 _ => hqz j
        (by omega)))) (seg_ex1 (r := 81) (v := .pred false) hv (by table_decide) (seg_411_419_skipG
        L g dt (fun j h1 _ => hqz j (by omega)))))) hn⟩

/-- From pc 316 to the first site of the loads or the stores. -/
theorem qenter (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hqz : ∀ j, 0 ≤ j → dt.q j = qZero) (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, SegD kernel asms L g n 316 (factsAt L g 316 dt) (qSite L g dt 0).pc
      (factsAt L g (qSite L g dt 0).pc dt) (addOk dt.w = true) := by
  obtain ⟨n, hn⟩ := qseg0 L g dt hqz hqb
  exact ⟨_, Raw.segD_iff (Raw.segD_pre (Seg.comp (seg_316_317 L g dt (ha.p25))
      (Seg.comp (seg_317_318 L g dt (ha.p11)) (seg_318_319 L g dt (ha.p10))))
      (Raw.segD_post (Raw.segD_post (segD_319_320 L g dt)
      (Seg.comp (seg_320_331 L g dt) (Seg.comp (seg_331_343 L g dt) (Seg.comp (seg_343_355 L g dt)
      (Seg.comp (seg_355_367 L g dt) (Seg.comp (seg_367_379 L g dt) (seg_379_387 L g dt))))))) hn))
    addOk_iff.symm⟩

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
