-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedG

@[expose] public section

/-! # The integer family of the float-tag engine

`absInt` (`Lemmas/Flow/TypedOps.lean`) lifted to `TypedF`: the registers of the old tags of an
`EnvF` (a register whose newest entry is a float tag is dropped) form the `Env` that `absOp`
reads. `absIntF` is sound for a stretch in which no assumption takes a segment or a local rule of
the instructions the integer family accepts (`PlainRules`, `PlainSegs`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

/-- The old tags of the registers `rs` in an environment: the newest entry of each, if it is an
old tag. The instruction's own registers are all the integer rule reads. -/
def viewOld (env : EnvF) : List Nat → Env
  | [] => []
  | r :: rs =>
    match env.lookup r with
    | some (.old t) => (r, t) :: viewOld env rs
    | _ => viewOld env rs

theorem viewOld_lookup {env : EnvF} {r : Nat} {tg : Tag} :
    ∀ {rs : List Nat}, (viewOld env rs).lookup r = some tg → env.lookup r = some (.old tg)
  | [], h => by simp [viewOld] at h
  | k :: rs, h => by
    unfold viewOld at h
    cases hk : env.lookup k with
    | none => simp only [hk] at h; exact viewOld_lookup h
    | some tk =>
      cases tk with
      | dat32 => simp only [hk] at h; exact viewOld_lookup h
      | dat64 => simp only [hk] at h; exact viewOld_lookup h
      | old t' =>
        simp only [hk] at h
        by_cases hr : (r == k) = true
        · simp only [List.lookup, hr] at h
          obtain rfl := beq_iff_eq.mp hr
          obtain rfl := Option.some.inj h
          exact hk
        · have hr' : (r == k) = false := by simpa using hr
          simp only [List.lookup, hr'] at h
          exact viewOld_lookup h

theorem typed_viewOld {env : EnvF} {t : TState} (h : TypedF env t) (rs : List Nat) :
    Typed (viewOld env rs) t := by
  intro r tg hl
  exact h r _ (viewOld_lookup hl)

/-- The integer family: what `absOp` accepts on the old tags. -/
def absIntF (env : EnvF) (op : Op) : Option (List (Nat × TagF)) :=
  (absOp (viewOld env (opRegs op)) op).map fun p => [(p.1, .old p.2)]

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem absIntF_sound {a b : Nat} (hN : PlainRules A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absIntF := by
  intro env op outs t h ha hb ht
  obtain ⟨⟨d, tg⟩, hab, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨v, hv, hok⟩ := exec_of_abs (L := L) (g := g) hab (typed_viewOld ht _)
  have hNo := hN t ha hb op ⟨viewOld env (opRegs op), by simp [hab]⟩
  have hex : execLocalA A L g t op = .ok (next (setReg t d v)) := by
    rw [execLocalA_noOverride hNo (hS t.pc ha hb)]
    exact hv
  refine ⟨_, hex, rfl, rfl, rfl, rfl, fun r hr => ?_, fun p hp => ?_⟩
  · have hrd : r ≠ d := fun e => hr (by simp [e])
    simp only [next, setReg]
    exact Function.update_of_ne hrd _ _
  · simp only [List.mem_singleton] at hp
    subst hp
    show tg.ok _
    simpa [next, setReg] using hok

/-- Two sound rules, the first one tried first, are a sound rule. -/
theorem AbsSound.or {a b : Nat} {f1 f2 : EnvF → Op → Option (List (Nat × TagF))}
    (h1 : AbsSound A L g a b f1) (h2 : AbsSound A L g a b f2) :
    AbsSound A L g a b (fun e o => (f1 e o).or (f2 e o)) := by
  intro env op outs t h ha hb ht
  cases h' : f1 env op with
  | some o1 =>
    simp only [h', Option.some_or] at h
    obtain rfl := Option.some.inj h
    exact h1 env op _ t h' ha hb ht
  | none => simp only [h', Option.none_or] at h; exact h2 env op _ t h ha hb ht

end PTX.Flow.TyG
