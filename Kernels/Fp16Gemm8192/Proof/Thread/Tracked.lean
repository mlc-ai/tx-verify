-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Warp
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueIndex

@[expose] public section

/-! # Every thread is followed by its machine

The roles' machines never give up on a thread: after a value they cannot follow (a read that
is not a cluster launch control response, a Tensor Memory value that does not convert, a
base address that does not rebuild) the thread is dead (`none`). The prologue's machine gives
up only on a shuffle that does not return the thread's warp index and on a dispatch that does
not match its warp, and along an execution neither happens: the shuffle returns the warp
index (`first_event`) and the dispatch follows it (`OnPath`). So in every execution every
thread is followed by its machine at each of its events (`tracked`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

theorem Loader.next_ne (L : Launch) (g : Nat) (d : Loader.D) (e : Event) :
    Loader.next L g d e ≠ some none := by
  intro h
  unfold Loader.next at h
  repeat' split at h
  all_goals simp_all

theorem Mma.next_ne (L : Launch) (g : Nat) (d : Mma.D) (e : Event) :
    Mma.next L g d e ≠ some none := by
  intro h
  unfold Mma.next at h
  repeat' split at h
  all_goals simp_all

theorem Scheduler.next_ne (L : Launch) (g : Nat) (d : Scheduler.D) (e : Event) :
    Scheduler.next L g d e ≠ some none := by
  intro h
  unfold Scheduler.next at h
  repeat' split at h
  all_goals simp_all

theorem Consumer.next_ne (L : Launch) (g : Nat) (d : Consumer.D) (e : Event) :
    Consumer.next L g d e ≠ some none := by
  intro h
  unfold Consumer.next at h
  repeat' split at h
  all_goals simp_all

/-- A prologue state on the thread's path continues or ends: its warp index is the thread's
after the shuffle, and the shuffle returns that index. -/
theorem Prologue.next_ne {L : Launch} {g : Nat} {p : Prologue.D} {e : Event}
    (hlt : Prologue.warpOf L g < 12) (hw : p.site ≠ .shfl → p.w = Prologue.warpOf L g)
    (hc : Prologue.Canon L g p)
    (hshfl : p.site = .shfl → ∃ pc, e = ⟨pc, .shfl .idx (b32 (Prologue.warpOf L g)) 0 31
      (b32 (Prologue.warpOf L g)) true⟩) :
    Prologue.next L g p e ≠ some none := by
  obtain ⟨s, w⟩ := p
  obtain ⟨-, -, -, hD, hE⟩ := hc
  simp only at hw hD hE hshfl
  intro h
  cases s with
  | shfl =>
    obtain ⟨pc, rfl⟩ := hshfl rfl
    have hm : (BitVec.ofNat 64 (Prologue.warpOf L g)).toNat = Prologue.warpOf L g := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    simp [Prologue.next, b32, hm, hlt] at h
  | wait =>
    have hw' := hw (by simp)
    subst hw'
    simp only [Prologue.next] at h
    split_ifs at h with h1 h2
    · simp at h
    · simp at h
    · apply h2
      exact ⟨by omega, trivial⟩
  | setMaxReg =>
    have hd := hD rfl
    simp only [Prologue.next] at h
    split_ifs at h with h1 h2 h3
    all_goals first | (simp at h; done) | omega
  | roleElect =>
    have he := hE rfl
    subst he
    simp only [Prologue.next] at h
    split at h <;> simp at h
  | _ =>
    simp only [Prologue.next] at h
    repeat' split at h
    all_goals simp at h

/-- A role's successor, mapped into the thread's states, is not `some none` when the role's own
successor is not. -/
theorem map_next_ne {α β : Type} (o : Option (Option α)) (F : α → β) (h : o ≠ some none) :
    o.map (Option.map F) ≠ some none := by
  rcases o with _ | _ | a
  · simp
  · exact absurd rfl h
  · simp

/-- The machine of a thread's code never gives up from a state the thread reaches. -/
theorem code_next_ne {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} (hg : g < L.threads)
    (hk : k < (X.tr g).length) {e : Event} (he : (X.tr g)[k]? = some e) {d : ThreadD}
    (hs : Frame.stateAt (code L) X g k = some (some d)) : (code L g).next d e ≠ some none := by
  cases d with
  | inr r =>
    cases r with
    | loader l => exact map_next_ne _ _ (Loader.next_ne L g l e)
    | mma m => exact map_next_ne _ _ (Mma.next_ne L g m e)
    | sched s => exact map_next_ne _ _ (Scheduler.next_ne L g s e)
    | cons c => exact map_next_ne _ _ (Consumer.next_ne L g c e)
  | inl p =>
    obtain ⟨hidx, hw, hcanon⟩ := (onPath_all hpre hX hg k hk.le).1 p hs
    refine Prologue.next_ne (Prologue.warpOf_lt hpre g) (fun hsh => hw ?_) hcanon (fun hsh => ?_)
    · rw [hidx]
      obtain ⟨s, w⟩ := p
      have := Prologue.fenceIdx_pos L g w
      cases s <;> simp only [Prologue.index] at hsh ⊢ <;> (try split_ifs) <;>
        first | omega | simp at hsh
    · have hk0 : k = 0 := by rw [hidx]; simp [Prologue.index, hsh]
      subst hk0
      exact ⟨_, first_event hpre hX hg he⟩

/-- **Every thread is followed by its machine** at each of its events. -/
theorem tracked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : Frame.Tracked (code L) X :=
  Frame.tracked_of fun _ _ _ _ hg he hs =>
    code_next_ne hpre hX hg (List.getElem?_eq_some_iff.mp he).1 he hs

end
end PTX.Kernels.Fp16Gemm8192.Proof
