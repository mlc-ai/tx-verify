-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Fire

@[expose] public section

/-! # What an instruction of each kind can fire

The generic half of `Ref/Kinds.lean` (read its header first): nothing here names the kernel.

* `SiteKind`: the kinds of event sites of the thread machine, one per constructor of
  `Thread.Site` (`Kinds/Table.lean` defines `Site.kind`).
* `firedAt k κ`: whether an event of kind `k` can be fired at a site of kind `κ`. An undefined
  behaviour event (`.ub`) can be fired anywhere.
* `opKind sub op`: the kind of the site at which a thread stands when it is about to execute
  the instruction `op` at sub-step `sub` (the sub-step is nonzero only between the events of
  one instruction: the second event of an `ldmatrix` or `stmatrix`, elements 1 to 3 of a
  vector load); `none` for an instruction that is no event site of this kernel.
* `fires_opKind`: **an event fired by an instruction of kind `κ` is of a kind that `κ` can
  fire.** For every instruction except the warp matrix ones this is the library's
  classification of templates (`eventTmpl_opTmpl`, `Lemmas/Flow/Fire.lean`); for `ldmatrix`
  and `stmatrix` the sub-step decides which of the two events it is (`fires_matrix`).
* `opKind_matrixLoad`, `opKind_matrixStore`, `opKind_load`: the kind of an instruction at a
  later sub-step, from its kind at sub-step 0 (so that the table needs one scan only).

The loads counted as `load` exclude the loads of the parameter space, which are local steps and
no event sites. A matrix load is classified only when every lane supplies a row
(`32 ≤ num * rows`, the `x4.m8n8` forms): only then is its first event always the read. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Flow

/-- The kinds of event sites: the constructors of `Thread.Site`. `matrixLoadMx` and
`matrixStoreWr` are the second events of an `ldmatrix` and a `stmatrix`; `loadEl1` to `loadEl3`
are the later elements of a vector load. -/
inductive SiteKind where
  | elect | shfl | mbarInit | fenceMbarInit | bar | load | mbarArrive | tensorCopy | mbarWait
  | fenceProxy | store | trap | matrixLoad | warpMma | matrixMove | matrixStore | bulkCommit
  | bulkWait | exit | matrixLoadMx | matrixStoreWr | loadEl1 | loadEl2 | loadEl3
  deriving DecidableEq, Repr

/-- **Whether an event of kind `k` can be fired at a site of kind `κ`.** Undefined behaviour
can be fired at every site; a kind of event that no site of the kernel fires (an atomic
read-modify-write, a linear copy, a Tensor Core event, …) at none. -/
def firedAt : PTX.Kind → SiteKind → Bool
  | .ub _, _ => true
  | .elect .., .elect => true
  | .shfl .., .shfl => true
  | .mbInit .., .mbarInit => true
  | .fenceMbarInit, .fenceMbarInit => true
  | .bar .., .bar => true
  | .rd .., .load | .rd .., .loadEl1 | .rd .., .loadEl2 | .rd .., .loadEl3
  | .rd .., .matrixLoad => true
  | .arrive .., .mbarArrive => true
  | .tensorIssue .., .tensorCopy | .tensorStore .., .tensorCopy => true
  | .wait .., .mbarWait => true
  | .fenceProxy .., .fenceProxy => true
  | .wr .., .store | .wr .., .matrixStoreWr => true
  | .matrix .., .matrixLoadMx | .matrix .., .warpMma | .matrix .., .matrixMove
  | .matrix .., .matrixStore => true
  | .bulkCommit, .bulkCommit => true
  | .bulkWait .., .bulkWait => true
  | .exit, .exit => true
  | _, _ => false

theorem firedAt_ub (f : Fault) (κ : SiteKind) : firedAt (.ub f) κ = true := by
  cases κ <;> rfl

/-- **The site kind of an instruction at a sub-step**, `none` if it is no event site of the
kernel. -/
def opKind (sub : Nat) : Op → Option SiteKind
  | .warp w => match w.kind with
    | .elect => some .elect
    | .shfl _ => some .shfl
    | _ => none
  | .mbarInit .. => some .mbarInit
  | .fenceMbarInit => some .fenceMbarInit
  | .barSync .. | .barSyncN .. => some .bar
  | .mem a => match a.kind, a.sem, a.nc, a.space with
    | .load, .weak, false, some .param => none
    | .load, .weak, false, _ => some (match sub with
      | 0 => .load
      | 1 => .loadEl1
      | 2 => .loadEl2
      | _ => .loadEl3)
    | .store, .weak, _, _ => some .store
    | _, _, _, _ => none
  | .mbarArrive .. => some .mbarArrive
  | .cpTensor .. | .cpTensorStore .. => some .tensorCopy
  | .mbarWait .. => some .mbarWait
  | .fence (.proxy ..) => some .fenceProxy
  | .trap => some .trap
  | .matrix i => match i.op with
    | .move m =>
      if m.store then some (if sub = 0 then .matrixStore else .matrixStoreWr)
      else if 32 ≤ m.num * m.rows then some (if sub = 0 then .matrixLoad else .matrixLoadMx)
      else none
    | .mma _ => some .warpMma
    | .transpose => some .matrixMove
  | .bulkCommit => some .bulkCommit
  | .bulkWait .. => some .bulkWait
  | .ret | .exit => some .exit
  | _ => none

set_option hygiene false in
/-- Close a goal whose hypothesis `h` says that an instruction of another class has a given
kind. -/
local macro "other_kind" : tactic => `(tactic| first
  | cases h
  | (simp only [opKind] at h
     first
       | cases h
       | (split at h <;> first | cases h | (split at h <;> first | cases h | simp at h))))

/-- A matrix load at a later sub-step is at its second event. -/
theorem opKind_matrixLoad {op : Op} {sub : Nat} (h : opKind 0 op = some .matrixLoad)
    (hs : sub ≠ 0) : opKind sub op = some .matrixLoadMx := by
  cases op
  case matrix i =>
    simp only [opKind] at h ⊢
    split at h
    · rename_i m hop
      split at h
      · simp at h
      · rename_i hst
        split at h
        · rename_i h32
          simp only [hst, Bool.false_eq_true, ↓reduceIte, h32, hs]
        · cases h
    · cases h
    · cases h
  case fence f => cases f <;> cases h
  all_goals other_kind

/-- A matrix store at a later sub-step is at its second event. -/
theorem opKind_matrixStore {op : Op} {sub : Nat} (h : opKind 0 op = some .matrixStore)
    (hs : sub ≠ 0) : opKind sub op = some .matrixStoreWr := by
  cases op
  case matrix i =>
    simp only [opKind] at h ⊢
    split at h
    · rename_i m hop
      split at h
      · rename_i hst
        simp only [hst, ↓reduceIte, hs]
      · split at h
        · simp at h
        · cases h
    · cases h
    · cases h
  case fence f => cases f <;> cases h
  all_goals other_kind

/-- A load at sub-step `k` is at element `k` of a vector load. -/
theorem opKind_load {op : Op} (h : opKind 0 op = some .load) :
    opKind 1 op = some .loadEl1 ∧ opKind 2 op = some .loadEl2 ∧ opKind 3 op = some .loadEl3 := by
  cases op
  case mem a =>
    simp only [opKind] at h ⊢
    split at h
    · cases h
    · exact ⟨rfl, rfl, rfl⟩
    · cases h
    · cases h
  case fence f => cases f <;> cases h
  all_goals other_kind

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState} {κ : SiteKind}

/-- **The events of a warp matrix instruction by sub-step.** A `stmatrix` first contributes
(a matrix event) and then writes; an `ldmatrix` of which every lane supplies a row first reads
and then receives (a matrix event); `mma` and `movmatrix` have one matrix event. -/
theorem fires_matrix {i : MatrixInstr} (hκ : opKind t.sub (.matrix i) = some κ)
    (hf : Fires pc (matrixTmpl L g t i) e o) : firedAt e.kind κ = true := by
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  unfold matrixTmpl at hf
  split at hf
  · split at hf
    · -- a matrix load or store
      rename_i m hrule hop
      simp only [opKind, hop] at hκ
      unfold matrixMoveTmpl at hf
      dsimp only at hf
      split at hf
      · -- `stmatrix`
        rename_i hst
        simp only [hst, ↓reduceIte, Option.some.injEq] at hκ
        split at hf
        · rename_i hs
          simp only [hs, ↓reduceIte] at hκ
          subst hκ
          split at hf
          · obtain ⟨rfl, -⟩ := hf; rfl
          · obtain ⟨recv, rfl, -⟩ := hf; rfl
        · rename_i hs
          simp only [hs, ↓reduceIte] at hκ
          subst hκ
          split at hf
          · obtain ⟨rfl, -⟩ := hf; rfl
          · obtain ⟨rfl, -⟩ := hf; rfl
      · -- `ldmatrix`
        rename_i hst
        simp only [hst, Bool.false_eq_true, ↓reduceIte] at hκ
        split at hκ
        · rename_i h32
          simp only [Option.some.injEq] at hκ
          split at hf
          · rename_i hs
            simp only [hs.2, ↓reduceIte] at hκ
            subst hκ
            split at hf
            · obtain ⟨rfl, -⟩ := hf; rfl
            · obtain ⟨bs, -, rfl, -⟩ := hf; rfl
          · rename_i hs
            have hs0 : t.sub ≠ 0 := fun h0 => hs ⟨by omega, h0⟩
            simp only [hs0, ↓reduceIte] at hκ
            subst hκ
            obtain ⟨recv, rfl, -⟩ := hf
            rfl
        · cases hκ
    · -- `movmatrix`
      rename_i d a hrule hop hd hs
      simp only [opKind, hop, Option.some.injEq] at hκ
      subst hκ
      split at hf
      · obtain ⟨rfl, -⟩ := hf; rfl
      · obtain ⟨recv, rfl, -⟩ := hf; rfl
    · -- `mma`
      rename_i s hrule hop
      simp only [opKind, hop, Option.some.injEq] at hκ
      subst hκ
      split at hf
      · obtain ⟨rfl, -⟩ := hf; rfl
      · obtain ⟨recv, rfl, -⟩ := hf; rfl
    · obtain ⟨rfl, -⟩ := hf
      exact firedAt_ub _ _
  · obtain ⟨rfl, -⟩ := hf
    exact firedAt_ub _ _

/-- **An event fired by an instruction of kind `κ` is of a kind that `κ` can fire.** -/
theorem fires_opKind {op : Op} (hκ : opKind t.sub op = some κ)
    (hf : Fires pc (eventTmpl A L g t op) e o) : firedAt e.kind κ = true := by
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t) op with ⟨f, hm⟩ | hev
  · rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    exact firedAt_ub _ _
  cases op
  case matrix i => exact fires_matrix hκ hf
  case trap =>
    obtain ⟨rfl, -⟩ := hf
    exact firedAt_ub _ _
  case warp w =>
    simp only [opKind] at hκ
    simp only [OpEv] at hev
    split at hκ
    · rename_i hk
      rw [hk] at hev
      obtain ⟨mask, k, hm⟩ := hev
      rw [hm] at hf
      obtain ⟨inst, leader, rfl, -⟩ := hf
      cases hκ
      rfl
    · rename_i md hk
      rw [hk] at hev
      obtain ⟨md', a, b, c, k, hm⟩ := hev
      rw [hm] at hf
      obtain ⟨recv, ok, rfl, -⟩ := hf
      cases hκ
      rfl
    · cases hκ
  case mem a =>
    simp only [opKind] at hκ
    simp only [OpEv] at hev
    split at hκ
    · cases hκ
    · rename_i hk hs hn _
      rw [hk, hs, hn] at hev
      obtain ⟨r, k, hm, -⟩ := hev
      rw [hm] at hf
      obtain ⟨bs, -, rfl, -⟩ := hf
      simp only [Option.some.injEq] at hκ
      subst hκ
      split <;> rfl
    · rename_i hk hs
      rw [hk, hs] at hev
      obtain ⟨r, bs, u, hm, -⟩ := hev
      rw [hm] at hf
      obtain ⟨rfl, -⟩ := hf
      cases hκ
      rfl
    · cases hκ
  case mbarInit =>
    obtain ⟨l, c, u, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case fenceMbarInit =>
    obtain ⟨u, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case barSync =>
    obtain ⟨id, u, c, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case barSyncN =>
    obtain ⟨id, u, c, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case mbarArrive =>
    obtain ⟨l, tx, u, c, r, s, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case cpTensor =>
    obtain ⟨a, s, u, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case cpTensorStore =>
    obtain ⟨a, s, u, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case mbarWait =>
    obtain ⟨l, p, k, a, s, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨ok, rfl, -⟩ := hf
    cases hκ
    rfl
  case fence f =>
    cases f with
    | thread _ _ => cases hκ
    | proxy k ord a =>
      obtain ⟨u, hm⟩ := hev
      rw [hm] at hf
      obtain ⟨rfl, -⟩ := hf
      cases hκ
      rfl
  case bulkCommit =>
    obtain ⟨u, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case bulkWait =>
    obtain ⟨md, n, u, hm⟩ := hev
    rw [hm] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case ret =>
    rw [show eventTmpl A L g t .ret = .exit from hev] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  case exit =>
    rw [show eventTmpl A L g t .exit = .exit from hev] at hf
    obtain ⟨rfl, -⟩ := hf
    cases hκ
    rfl
  all_goals cases hκ

end PTX.Kernels.FlashKdaFwd.Proof.Ref
