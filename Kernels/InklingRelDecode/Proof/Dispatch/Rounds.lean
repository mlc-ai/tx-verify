-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.RoleByte
public import Kernels.InklingRelDecode.Proof.Lib.BarZero

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Flow PTX.Proof

/-- The sites a worker's dispatch round can stand at: round 0 reads the launch's role word, so
the retry path (`badSync`) is not taken; round 1 reads the exit word. -/
def round0 : List Site :=
  [.head, .sync, .read, .idleDec, .idleSync, .idleSyncAgain, .idleInc, .loaderEntry, .mmaEntry]

def round1 : List Site := [.head, .sync, .read, .exitSync, .exitDealloc, .ret]

def Allowed (d : D) : Prop :=
  (d.round = 0 ∧ d.site ∈ round0) ∨ (d.round = 1 ∧ d.site ∈ round1)

/-- The final rendezvous (pc 2853) is behind the state. -/
def finalDone (d : D) : Nat := if d.site = .exitDealloc ∨ d.site = .ret then 1 else 0

theorem allowed_init : Allowed ⟨.head, 0⟩ := .inl ⟨rfl, by decide⟩

theorem allowed_back : Allowed ⟨.head, 1⟩ := .inr ⟨rfl, by decide⟩

theorem allowed_next {L g d ev dn} (low : 4≤g%L.block/32) (high : g%L.block/32<8)
    (read : ∀ a bs, d.site=.read → ev.kind=.rd a bs →
      bs=[(b32 (if d.round=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?])
    (old : Allowed d) (step : next L g d ev=some (some dn)) : Allowed dn := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at step
    split at step <;> try contradiction
    rename_i a bs kd
    have hb := read a bs rfl kd
    let idx : Fin 4 := ⟨g%L.block/32-4,by omega⟩
    have pick := role_target idx (decide (r=0))
    rw [hb] at step
    simp only [decide_eq_true_eq] at pick
    rw [pick] at step
    simp only [Option.map_some, Option.some.injEq] at step
    subst dn
    rcases old with ⟨hr,-⟩|⟨hr,-⟩ <;> subst hr
    · by_cases h2 : idx.val=2 <;> by_cases h3 : idx.val=3 <;>
        simp [Allowed, round0, h2, h3]
    · simp [Allowed, round1]
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals try contradiction
  all_goals cases step
  all_goals simp [Allowed, round0, round1] at old ⊢
  all_goals omega

private theorem target_open (n : Nat) : target n ≠ .exitDealloc ∧ target n ≠ .ret := by
  unfold target
  split <;> simp

private theorem read_open {bs s} (h : readTarget bs = some s) : s ≠ .exitDealloc ∧ s ≠ .ret := by
  unfold readTarget at h
  cases hr : (rebuild 3 bs).toOption with
  | none => simp [hr] at h
  | some v =>
    cases hx : (extendLoaded (.zero 32) 8 v).toOption with
    | none => simp [hr, hx] at h
    | some x =>
      simp [hr, hx] at h
      split at h <;> try contradiction
      cases h
      exact target_open _

theorem finalDone_next {L g d ev dn} (step : next L g d ev=some (some dn)) :
    finalDone dn = finalDone d + (if d.site.pc = 2853 then 1 else 0) := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at step
    split at step <;> try contradiction
    obtain ⟨dest, found, h⟩ := Option.map_eq_some_iff.mp step
    cases h
    obtain ⟨h1, h2⟩ := read_open found
    simp [finalDone, Site.pc, h1, h2]
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp [finalDone, Site.pc]

/-- The loader and the MMA warp are never at an idle site in the first round: their byte calls
a role. -/
def Busy (warp : Nat) (d : D) : Prop :=
  (warp = 6 ∨ warp = 7) → d.round = 0 →
    d.site = .head ∨ d.site = .sync ∨ d.site = .read ∨ d.site = .loaderEntry ∨
      d.site = .mmaEntry

theorem busy_init (warp : Nat) : Busy warp ⟨.head, 0⟩ := fun _ _ => .inl rfl

theorem busy_next {L g d ev dn} (low : 4≤g%L.block/32) (high : g%L.block/32<8)
    (read : ∀ a bs, d.site=.read → ev.kind=.rd a bs →
      bs=[(b32 (if d.round=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?])
    (old : Busy (g%L.block/32) d) (step : next L g d ev=some (some dn)) :
    Busy (g%L.block/32) dn := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    have dst := read_dst low high (fun a bs kd => read a bs rfl kd) step
    subst dst
    intro w z
    by_cases init : r=0 <;> by_cases w6 : g%L.block/32=6 <;> by_cases w7 : g%L.block/32=7 <;>
      simp_all
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals try contradiction
  all_goals cases step
  all_goals intro w z
  all_goals simp_all [Busy]

/-- The first three sites stay in their round. -/
theorem round_stay {L g d ev dn} (h : d.site = .head ∨ d.site = .sync ∨ d.site = .read)
    (step : next L g d ev=some (some dn)) : dn.round = d.round := by
  obtain ⟨s,r⟩ := d
  simp only at h
  rcases h with rfl | rfl | rfl
  · cases step; rfl
  · cases step; rfl
  · simp only [next] at step
    split at step <;> try contradiction
    obtain ⟨_,_,h⟩ := Option.map_eq_some_iff.mp step
    cases h
    rfl

/-- A step of the loader or MMA warp in its first round stays in it. -/
theorem busy_round {L g w d ev dn} (b : Busy w d) (hw : w = 6 ∨ w = 7) (z : d.round = 0)
    (step : next L g d ev=some (some dn)) : dn.round = 0 := by
  rcases b hw z with h | h | h | h | h
  · exact (round_stay (.inl h) step).trans z
  · exact (round_stay (.inr (.inl h)) step).trans z
  · exact (round_stay (.inr (.inr h)) step).trans z
  all_goals
    obtain ⟨s, r⟩ := d
    simp only at h
    subst h
    simp [next] at step

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
