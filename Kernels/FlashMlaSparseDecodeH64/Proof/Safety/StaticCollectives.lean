-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StaticCollectiveEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RegisterRequestTrace

public section

/-! # Collective safety checks fixed by the instruction stream -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX StaticCollectiveEvents

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- No cluster barrier record can fault in this kernel. -/
theorem no_clusterFault (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ ClusterFault L X := by
  rintro ⟨_, _, _, _, r, _, hSrc, _, hPerform, hFault⟩
  cases r with
  | exit =>
    simp only [ClusterBarrier.Record.perform, ClusterBarrier.perform] at hPerform
    split at hPerform
    · cases hPerform
      cases hFault
    · cases hPerform
  | arrival _ _ _ lanes | wait _ _ lanes =>
    simp only [ClusterBarrier.Record.perform] at hPerform
    split at hPerform
    · rename_i hValid
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil lanes (fun hn => by
        have h := (of_decide_eq_true hValid).2.2.2.1
        simp only [ne_eq, List.map_eq_nil_iff] at h
        exact h hn)
      obtain ⟨_, _, _, _, he⟩ := hSrc p hp
      exact no_cluster hX he
    · cases hPerform
      cases hFault

/-- There is no cluster barrier that can disagree with a lane or be skipped by an exit. -/
theorem no_aligned_cluster (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ (AlignedClass.cluster.Divergent L kernel X ∨ AlignedClass.cluster.Exited L kernel X) := by
  rintro (h | h)
  · obtain ⟨_, _, _, _, _, _, _, _, _, he, _, _, _, _⟩ :=
      (AlignedClass.divergent_cluster_iff L).mp h
    exact no_cluster hX he
  · obtain ⟨_, _, _, _, _, _, he, _, _, _⟩ := (AlignedClass.exited_cluster_iff L).mp h
    exact no_cluster hX he

/-- There is no aligned matrix operation that can disagree with a lane or be skipped by an exit. -/
theorem no_aligned_matrix (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ (AlignedClass.matrix.Divergent L kernel X ∨ AlignedClass.matrix.Exited L kernel X) := by
  rintro (⟨i, _, tag, _, kind, _, _, he, _, hMember, _, _, _, _⟩ | h)
  · have hMatrix : isMatrix ⟨tag, kind⟩ = true := hMember
    rw [GlobalWrites.no_matrix hX he] at hMatrix
    cases hMatrix
  · obtain ⟨g, j, tag, op, own, recv, _, he, _, _⟩ := AlignedClass.exited_matrix_old L h
    have hf := GlobalWrites.no_matrix hX he
    cases hf

/-- No arrival-form named barrier can disagree with another lane. -/
theorem no_barArriveMismatch (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ BarArriveMismatch L X := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, he, _, _, _⟩
  exact no_bar_arrive hX he

private theorem prior_of_no_requests (es : List Event) (start : Option Nat)
    (h : es.countP SetMaxNReg.isRequest = 0) :
    es.foldl (fun old ev => match ev.kind with
      | .setMaxReg _ n _ => some n
      | _ => old) start = start := by
  induction es with
  | nil => rfl
  | cons e tail ih =>
    rw [List.countP_cons] at h
    rw [List.foldl_cons]
    cases hk : e.kind
    case setMaxReg =>
      have hReq : SetMaxNReg.isRequest e = true := by simp [SetMaxNReg.isRequest, hk]
      simp [hReq] at h
    all_goals apply ih; omega

private theorem same_group_wg {P : Params} (hpre : Pre P L mem0) {g h : Nat}
    (hw : SetMaxNReg.SameGroup L g h) : wgOf L g = wgOf L h := by
  obtain ⟨_, hw⟩ := hw
  simpa only [wgOf, tidOf_eq hpre, hpre.block] using hw

private theorem same_warp_wg {P : Params} (hpre : Pre P L mem0) {g h : Nat}
    (hw : SameWarp L g h) : wgOf L g = wgOf L h := by
  obtain ⟨_, hw⟩ := hw
  simp only [hpre.block] at hw
  simp only [wgOf, tidOf_eq hpre]
  omega

/-- Each register adjustment is the first request and agrees with its entire warpgroup. -/
theorem no_setMaxNRegUnsafe {P : Params} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) : ¬ SetMaxNReg.Unsafe L X := by
  rintro ⟨⟨g, i⟩, tag, inc, n, inst, hr, hu⟩
  obtain ⟨ho, hData⟩ := RegisterRequestTrace.request_payload hpre hX hs ht hr
  rcases hu with ⟨_, hp, _⟩ | hPartial |
      ⟨⟨g', i'⟩, tag', inc', n', inst', hGroup, hr', _, hDiff⟩ | ⟨hLate, _⟩
  · have hPrior : SetMaxNReg.prior X (g, i) = none :=
      prior_of_no_requests _ none ho
    rw [hPrior] at hp
    cases hp
  · have hn := Nat.mod_lt g (by decide : 0 < 384)
    simp only [hpre.block] at hPartial
    omega
  · obtain ⟨_, hData'⟩ := RegisterRequestTrace.request_payload hpre hX hs ht hr'
    have hSame := same_group_wg hpre hGroup
    change wgOf L g = wgOf L g' at hSame
    rw [hSame, ← hData'] at hData
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hData
    exact hDiff.elim (fun h => h rfl) (fun h => h rfl)
  · rw [ho] at hLate
    omega

/-- An aligned register request agrees across each issuing warp and precedes every exit. -/
theorem no_aligned_setMaxNReg {P : Params} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ (AlignedClass.setMaxReg.Divergent L kernel X ∨
      AlignedClass.setMaxReg.Exited L kernel X) := by
  rintro (h | h)
  · obtain ⟨⟨g, i⟩, ⟨g', i'⟩, _, _, _, _, _, _, _, _, hWarp, hr, hr', _, hDiff⟩ :=
      (AlignedClass.divergent_setMaxReg_iff L).mp h
    exact hDiff (RegisterRequestTrace.same_source hpre hX hs ht hr hr' (same_warp_wg hpre hWarp))
  · obtain ⟨⟨g, i⟩, _, _, _, _, hr, h, j, _, _, _, he, hShort⟩ :=
      AlignedClass.exited_setMaxReg_old L h
    have ho := (RegisterRequestTrace.request_payload hpre hX hs ht hr).1
    have heo := RegisterRequestTrace.exit_ordinal hX hs ht he
    rw [ho, heo] at hShort
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
