-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Uses
import Kernels.InklingRelDecode.Proof.Lib.PollEvent

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow MbarRow PTX.MbarRow

/-- Visits to one slot among the first n polls of a sequence starting at block a. -/
def visits (a n : Nat) (s : Fin 3) := (a+n+2-s.val)/3 - (a+2-s.val)/3

private theorem visit_step (a n : Nat) (s : Fin 3) :
    visits a (n+1) s = visits a n s + if (a+n)%3 = s.val then 1 else 0 := by
  unfold visits
  have hs := s.isLt
  split <;> omega

/-- Prefix induction comparing a PC counter with a single-slot counter. -/
theorem slot_count {es : List Event} {l : Loc} {pc a : Nat} {s : Fin 3}
    (classify : ∀ k e, es[k]? = some e →
      (okPoll l e = true ↔ okPollAt pc e = true ∧
        (a + pollRound pc (es.take k)) % 3 = s.val)) (k : Nat) :
    okPolls l (es.take k) = visits a (pollRound pc (es.take k)) s := by
  apply Lib.PollEvent.count_index (fun n => decide ((a+n)%3=s.val))
    (fun n => visits a n s) (by simp [visits])
  · intro n; simpa using visit_step a n s
  · simpa using classify

theorem use_cta {Q L X g k e r c s} (rows : MbarRows Q L X) (hg : g < L.threads)
    (he : X.get (g,k) = some e) (hm : Frame.MbarOf e (Ring.obj r L c s)) : g / L.block = c := by
  cases mbar_use rows hg he hm with
  | startup _ h | dispatch _ h => cases h
  | prologue _ h | softmax _ h | epilogue _ h | loader _ h | mma _ h =>
    cases h <;> exact (congrArg Loc.cta (show r.obj L c s = loc L g _ from by assumption)).symm

/-- A wait naming a KV slot selects the worker warp, site, slot and parity. -/
theorem wait_info {Q L X g k pc q ok acq sc r c s} (rows : MbarRows Q L X) (hg : g < L.threads)
    (he : X.get (g,k) = some ⟨pc,.wait (Ring.obj r L c s) q ok acq sc⟩) :
    g / L.block = c ∧ acq = true ∧ sc = .cta ∧
      match r with
      | .empty => g % L.block / 32 = 6 ∧ pc = 2374 ∧ s = slot3 (loaderRound Q L X g k) ∧
          q = 1 - loaderRound Q L X g k / 3 % 2
      | .ready => g % L.block / 32 = 7 ∧ pc = 2462 ∧ s = slot3 (roundAt X g k 2462) ∧
          q = roundAt X g k 2462 / 3 % 2 := by
  have hc := use_cta rows hg he rfl
  refine ⟨hc,?_⟩
  have hu := ring_use rows hg he (r := r) (s := s) (by rfl)
  generalize hh : (Event.mk pc (.wait (Ring.obj r L c s) q ok acq sc)) = ev at hu
  cases hu with
  | init _ hk => cases hh; cases hk
  | preload _ hk | arrive _ _ hk => cases hh; cases hk
  | preloadCopy _ h | copy _ _ h => cases hh; obtain ⟨_,_,hk,_⟩ := h; cases hk
  | notify _ _ h => cases hh; obtain ⟨_,hk,_⟩ := h; cases hk
  | emptyWait hp hw h | readyWait hp hw h =>
    cases hh
    obtain ⟨b,hk⟩ := h
    obtain ⟨_,rfl,_,rfl,rfl⟩ := Kind.wait.inj hk
    exact ⟨rfl,rfl,hw,hp,rfl,rfl⟩

def Ring.site : Ring → Nat | .ready => 2462 | .empty => 2374
def Ring.warp : Ring → Nat | .ready => 7 | .empty => 6
def Ring.start (Q : Params) (L : Launch) (c : Nat) : Ring → Nat
  | .ready => 0 | .empty => Iface.preloadCount Q L c

/-- Each of the two polling sites addresses exactly its ordinal slot. -/
theorem at_slot {Q L X g k r l q ok acq sc} (rows : MbarRows Q L X) (hg : g < L.threads)
    (hw : g % L.block / 32 = Ring.warp r)
    (he : X.get (g,k) = some ⟨r.site,.wait l q ok acq sc⟩) :
    l = r.obj L (g / L.block) (slot3 (r.start Q L (g / L.block) + roundAt X g k r.site)) := by
  cases r with
  | ready =>
    have hu := rows.mma hg he (show MmaAt L g 2462 from ⟨hw,by decide,by decide⟩) (l := l) rfl
    cases hu with
    | readyWait _ hl _ =>
      simpa only [Ring.start,Ring.site,Nat.zero_add,Ring.obj,Ring.offset,loc] using hl
    | pWait h _ _ | sCommit h _ _ | emptyCommit h _ _ | doneCommit h _ _ | finalCommit h _ _ =>
      simp [Ring.site] at h
  | empty =>
    have hat : LoaderAt L g 2374 := ⟨hw,by decide,by decide⟩
    have hu := rows.loader hg he hat (l := l) rfl
    cases hu with
    | emptyWait _ hl _ => exact hl
    | readyArrive h _ _ _ => cases h
    | readyCopy h _ _ _ => simp [Ring.site] at h

theorem poll_count {Q L X g r} (rows : MbarRows Q L X) (hg : g < L.threads)
    (hw : g % L.block / 32 = Ring.warp r) (s : Fin 3) (k : Nat) :
    okPolls (r.obj L (g / L.block) s) ((X.tr g).take k) =
      visits (r.start Q L (g / L.block)) (roundAt X g k r.site) s := by
  apply slot_count
  intro j e he
  constructor
  · intro h
    obtain ⟨p,q,ac,sc,rfl⟩ := Lib.PollEvent.obj_iff.mp h
    obtain ⟨_,_,_,hi⟩ := wait_info rows hg he
    cases r <;> obtain ⟨_,rfl,rfl,_⟩ := hi
    all_goals
      exact ⟨Lib.PollEvent.at_iff.mpr ⟨_,_,_,_,rfl⟩,
        by simp [Ring.start,Ring.site,slot3,loaderRound,roundAt]⟩
  · rintro ⟨hp,hs⟩
    obtain ⟨l,q,ac,sc,rfl⟩ := Lib.PollEvent.at_iff.mp hp
    have hl := at_slot rows hg hw he
    have hslot : slot3 (r.start Q L (g / L.block) + roundAt X g j r.site) = s := Fin.ext hs
    rw [hslot] at hl
    exact Lib.PollEvent.obj_iff.mpr ⟨_,_,_,_,by rw [hl]⟩

/-- A preloaded empty slot starts one unit later in the MMA-to-loader notification history. -/
def preload (Q : Params) (L : Launch) (c : Nat) (s : Fin 3) : Nat :=
  if s.val < Iface.preloadCount Q L c then 1 else 0

private theorem complement (a n : Nat) (ha : a ≤ 3) :
    (1 - (a+n)/3%2)%2 =
      (visits a n (slot3 (a+n)) + (1 - (if (a+n)%3 < a then 1 else 0)))%2 := by
  have hj : (a+n+2-(a+n)%3)/3 = (a+n)/3 := by omega
  unfold visits slot3
  dsimp only
  rw [hj]
  by_cases h : (a+n)%3 < a
  · simp only [h,↓reduceIte]
    have : (a+2-(a+n)%3)/3 = 1 := by omega
    rw [this]
    omega
  · simp only [h,↓reduceIte]
    have : (a+2-(a+n)%3)/3 = 0 := by omega
    rw [this]
    omega

theorem wait_parity {Q L X g k pc q ok acq sc r c s} (rows : MbarRows Q L X) (hg : g < L.threads)
    (he : X.get (g,k) = some ⟨pc,.wait (Ring.obj r L c s) q ok acq sc⟩) :
    q % 2 = (okPolls (r.obj L c s) ((X.tr g).take k) +
      (match r with | .ready => 0 | .empty => 1 - preload Q L c s)) % 2 := by
  obtain ⟨rfl,_,_,hi⟩ := wait_info rows hg he
  cases r with
  | ready =>
    obtain ⟨hw,_,rfl,rfl⟩ := hi
    rw [poll_count (r := .ready) rows hg hw]
    simp only [Ring.start,Ring.site,visits,slot3,Nat.zero_add,Nat.add_zero]
    omega
  | empty =>
    obtain ⟨hw,_,rfl,rfl⟩ := hi
    rw [poll_count (r := .empty) rows hg hw]
    have ha : Iface.preloadCount Q L (g / L.block) ≤ 3 := Nat.min_le_left ..
    exact complement _ _ ha

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
