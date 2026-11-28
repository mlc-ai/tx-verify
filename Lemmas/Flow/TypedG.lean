-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.HavocTyped
public import Lemmas.Flow.FmaTotal

@[expose] public section

/-! # A typed crossing with float tags

`Lemmas/Flow/HavocTyped.lean` crosses a stretch of integer, move and conversion instructions that
cannot fail on registers of known tags. Its `Tag` has no float. This file generalizes the crossing
over a *family* of abstract instruction rules: `TagF` adds `dat32` (a value `classify` reads as an
`.f32` datum: a number, a zero, an infinity or a NaN) to the old tags, and the engine
(`crossF`, `SegQF.of_typed`) takes the abstract rule `abs : EnvF → Op → Option (List (Nat × TagF))`
together with its soundness `AbsSound` (the instruction's local step, under the assumptions at
every pc of the stretch, succeeds, writes exactly the listed registers with values of the listed
tags, and moves to the next pc). The families (integer: `TypedOpsF.lean`, float: `TypedFloat*`) are
proved sound once; a stretch is then a segment by one `decide`-checked Boolean `checkF`. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged

/-- An `.f32` datum of four bytes that is no slice of a wider value. -/
def Dat32 (x : Value) : Prop := F32Dat x ∧ x.bytes = 4 ∧ ∀ w o n, x ≠ .slice w o n

/-- A 64-bit value: a bit pattern, or a pair of `.f32` data. -/
def Dat64 (x : Value) : Prop :=
  (∃ y, x = .bits 64 y) ∨ ∃ lo hi, x = .pair lo hi ∧ Dat32 lo ∧ Dat32 hi

theorem dat32_bits (x : BitVec 64) : Dat32 (.bits 32 x) := ⟨f32Dat_bits x, rfl, nofun⟩

/-- What a register holds: an old tag, an `.f32` datum (any number, infinity or NaN), or a
64-bit value of two of them. -/
inductive TagF where
  | old (t : Tag)
  | dat32
  | dat64
  deriving DecidableEq, Repr

def TagF.ok : TagF → Option Value → Prop
  | .old t, v => t.ok v
  | .dat32, v => ∃ x, v = some x ∧ Dat32 x
  | .dat64, v => ∃ x, v = some x ∧ Dat64 x

abbrev EnvF := List (Nat × TagF)

def TypedF (env : EnvF) (t : TState) : Prop :=
  ∀ r tg, env.lookup r = some tg → tg.ok (t.regs r)

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The abstract rule `abs` is sound for the instructions at the pcs `[a, b)`: from a state of
tags `env` at such a pc whose code is the unguarded local `op`, the local step succeeds, writes only
the listed registers, with values of the listed tags, and moves to the next pc. -/
def AbsSound (A : List Assumption) (L : Launch) (g a b : Nat)
    (abs : EnvF → Op → Option (List (Nat × TagF))) : Prop :=
  ∀ (env : EnvF) (op : Op) (outs : List (Nat × TagF)) (t : TState), abs env op = some outs →
    a ≤ t.pc → t.pc < b → TypedF env t → ∃ u, execLocalA A L g t op = .ok u ∧
      u.pc = t.pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault ∧
      (∀ r, r ∉ outs.map Prod.fst → u.regs r = t.regs r) ∧ ∀ p ∈ outs, p.2.ok (u.regs p.1)

/-- The abstract run of a stretch: the tags after it and the registers it writes. -/
def runF (abs : EnvF → Op → Option (List (Nat × TagF))) (env : EnvF) :
    List Instr → Option (EnvF × List Nat)
  | [] => some (env, [])
  | ins :: rest =>
    if ins.guard.isNone && ins.op.isLocal then
      (abs env ins.op).bind fun outs =>
        (runF abs (outs ++ env) rest).map fun (e, w) => (e, outs.map Prod.fst ++ w)
    else none

theorem lookup_append_some {α : Type} : ∀ {l1 l2 : List (Nat × α)} {r : Nat} {x : α},
    (l1 ++ l2).lookup r = some x →
    l1.lookup r = some x ∨ (l1.lookup r = none ∧ l2.lookup r = some x)
  | [], l2, r, x, h => .inr ⟨rfl, h⟩
  | (k, y) :: l1, l2, r, x, h => by
    by_cases hr : (r == k) = true
    · simp only [List.cons_append, List.lookup, hr] at h
      simp only [List.lookup, hr]
      exact .inl h
    · simp only [List.cons_append, List.lookup, (by simpa using hr : (r == k) = false)] at h ⊢
      exact lookup_append_some h

theorem lookup_none_keys {α : Type} : ∀ {l : List (Nat × α)} {r : Nat},
    l.lookup r = none → r ∉ l.map Prod.fst
  | [], r, _ => by simp
  | (k, y) :: l, r, h => by
    by_cases hr : (r == k) = true
    · simp [List.lookup, hr] at h
    · simp only [List.lookup, (by simpa using hr : (r == k) = false)] at h
      have := lookup_none_keys h
      have hne : r ≠ k := by simpa using hr
      simp [this, hne]

theorem lookup_mem' {α : Type} : ∀ {l : List (Nat × α)} {r : Nat} {x : α},
    l.lookup r = some x → (r, x) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, y) :: l, r, x, h => by
    by_cases hr : (r == k) = true
    · simp only [List.lookup, hr] at h
      obtain rfl := beq_iff_eq.mp hr
      obtain rfl := Option.some.inj h
      simp
    · simp only [List.lookup, (by simpa using hr : (r == k) = false)] at h
      exact List.mem_cons_of_mem _ (lookup_mem' h)

theorem typedF_cons {env : EnvF} {t u : TState} {outs : List (Nat × TagF)}
    (ht : TypedF env t) (hw : ∀ r, r ∉ outs.map Prod.fst → u.regs r = t.regs r)
    (hv : ∀ p ∈ outs, p.2.ok (u.regs p.1)) : TypedF (outs ++ env) u := by
  intro r tg h
  rcases lookup_append_some h with h1 | ⟨h1, h2⟩
  · exact hv _ (by simpa using lookup_mem' h1)
  · rw [hw r (lookup_none_keys h1)]
    exact ht r tg h2


/-- The tag of a program counter's invariant: the registers have the tags `qt pc`. -/
def QTF (qt : Nat → EnvF) (t : TState) : Prop := TypedF (qt t.pc) t

variable {abs : EnvF → Op → Option (List (Nat × TagF))}

/-- **The crossing**: the `n` instructions from `pc` to `b` end at `b` in a state of the tags of
their abstract run, writing only the registers the run lists. -/
theorem crossF_aux {a b : Nat} (hlen : b ≤ K.code.length) (hA : AbsSound A L g a b abs) :
    ∀ (n pc : Nat) (env env' : EnvF) (w : List Nat) (t : TState), a ≤ pc → pc + n = b →
      t.pc = pc → t.sub = 0 → t.acc = [] → t.fault = none → TypedF env t →
      runF abs env ((K.code.drop pc).take n) = some (env', w) →
      ∃ u, run K A L g n t = some u ∧ u.pc = b ∧ u.sub = 0 ∧ u.acc = [] ∧
        u.fault = none ∧ TypedF env' u ∧ ∀ r, r ∉ w → u.regs r = t.regs r := by
  intro n
  induction n with
  | zero =>
    intro pc env env' w t _ hb hpc hsub hacc hf ht hr
    simp only [List.take_zero, runF, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨t, rfl, by omega, hsub, hacc, hf, ht, fun _ _ => rfl⟩
  | succ n ih =>
    intro pc env env' w t ha hb hpc hsub hacc hf ht hr
    have hlt : pc < K.code.length := by omega
    rw [Havoc.take_cons hlt] at hr
    simp only [runF, Bool.and_eq_true] at hr
    split_ifs at hr with hg
    obtain ⟨hguard, hl⟩ := hg
    obtain ⟨outs, hab, hr2⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨⟨e2, w2⟩, hr3, hr4⟩ := Option.map_eq_some_iff.mp hr2
    have hcode : K.code[pc]? = some ⟨none, K.code[pc].op⟩ := by
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq]
      have hg := Option.isNone_iff_eq_none.mp hguard
      generalize K.code[pc] = ins at hg ⊢
      rcases ins with ⟨gd, op⟩
      simp only at hg
      rw [hg]
    obtain ⟨v, hex, hpcv, hsv, hav, hfv, hwr, hok⟩ :=
      hA env K.code[pc].op outs t hab (by omega) (by omega) ht
    have htau := tau_of_ok (A := A) (L := L) (g := g) (by rw [hpc]; exact hcode) hl hf hex
    have hty := typedF_cons ht hwr hok
    simp only [Prod.mk.injEq] at hr4
    obtain ⟨rfl, rfl⟩ := hr4
    obtain ⟨u, hu, hpcu, hsu, hau, hfu, htu, hfr⟩ :=
      ih (pc + 1) (outs ++ env) e2 w2 v (by omega) (by omega) (by omega) (by rw [hsv]; exact hsub)
        (by rw [hav]; exact hacc) (by rw [hfv]; exact hf) hty hr3
    refine ⟨u, ?_, hpcu, hsu, hau, hfu, htu, fun r hr' => ?_⟩
    · show (tauStep K A L g t).bind (run K A L g n) = some u
      rw [tauStep_iff.mpr htau]
      exact hu
    simp only [List.mem_append, not_or] at hr'
    rw [hfr r hr'.2, hwr r hr'.1]


/-- The tag `have` serves a use that needs `need`. -/
def TagF.sat : Option TagF → TagF → Bool
  | some (.old h), .old n => Havoc.Tag.sat (some h) n
  | some (.old (.bits w)), .dat32 | some (.old (.nz w)), .dat32 => w == 32
  | some (.old (.bits w)), .dat64 | some (.old (.nz w)), .dat64 => w == 64
  | some .dat32, .dat32 | some .dat64, .dat64 => true
  | _, _ => false

theorem TagF.sat_ok {h : Option TagF} {need : TagF} {v : Option Value}
    (hs : TagF.sat h need = true) (hh : ∀ tg, h = some tg → tg.ok v) : need.ok v := by
  cases h with
  | none => cases need <;> simp [TagF.sat] at hs
  | some tg =>
    have := hh tg rfl
    cases tg with
    | old h' =>
      cases need with
      | old n => exact Havoc.Tag.sat_ok hs (fun t' e => by cases e; exact this)
      | dat32 =>
        cases h' <;> simp only [TagF.sat, reduceCtorEq, beq_iff_eq] at hs
        · rename_i w
          have hw : w = 32 := by simpa using hs
          subst hw
          obtain ⟨x, hx⟩ := this
          exact ⟨_, hx, dat32_bits x⟩
        · rename_i w
          have hw : w = 32 := by simpa using hs
          subst hw
          obtain ⟨x, hx, -⟩ := this
          exact ⟨_, hx, dat32_bits x⟩
      | dat64 =>
        cases h' <;> simp only [TagF.sat, reduceCtorEq, beq_iff_eq] at hs
        · rename_i w
          have hw : w = 64 := by simpa using hs
          subst hw
          obtain ⟨x, hx⟩ := this
          exact ⟨_, hx, .inl ⟨x, rfl⟩⟩
        · rename_i w
          have hw : w = 64 := by simpa using hs
          subst hw
          obtain ⟨x, hx, -⟩ := this
          exact ⟨_, hx, .inl ⟨x, rfl⟩⟩
    | dat32 => cases need <;> simp [TagF.sat] at hs ⊢; exact this
    | dat64 => cases need <;> simp [TagF.sat] at hs ⊢; exact this

/-- The check of a typed piece from `a` to `b`. -/
def checkF (abs : EnvF → Op → Option (List (Nat × TagF))) (qt : Nat → EnvF) (a b : Nat)
    (Ft : Env) (Gk : List Nat) (ops : List Instr) : Bool :=
  match runF abs (qt a ++ Ft.map fun p => (p.1, TagF.old p.2)) ops with
  | none => false
  | some (e, w) => (qt b).all (fun p => TagF.sat (e.lookup p.1) p.2) &&
      Gk.all (fun k => !w.contains k)


theorem lookup_map_old : ∀ {Ft : Env} {r : Nat} {tg : TagF},
    (Ft.map fun p => (p.1, TagF.old p.2)).lookup r = some tg →
    ∃ t, Ft.lookup r = some t ∧ tg = .old t
  | [], r, tg, h => by simp at h
  | p :: ps, r, tg, h => by
    by_cases hr : (r == p.1) = true
    · simp only [List.map_cons, List.lookup, hr] at h
      exact ⟨p.2, by simp [List.lookup, hr], (Option.some.inj h).symm⟩
    · have hr' : (r == p.1) = false := by simpa using hr
      simp only [List.map_cons, List.lookup, hr'] at h
      obtain ⟨t, h1, h2⟩ := lookup_map_old h
      exact ⟨t, by simp [List.lookup, hr', h1], h2⟩

theorem typedF_facts {Ft : Env} {t : TState} (h : Typed Ft t) :
    TypedF (Ft.map fun p => (p.1, TagF.old p.2)) t := by
  intro r tg hl
  obtain ⟨t', h1, rfl⟩ := lookup_map_old hl
  exact h r t' h1

/-- **A typed piece runs**: from a state of the tags `qt a` and the facts `F`, the piece's
`b - a` local steps end at `b` in a state of the tags `qt b`, the registers the stretch does not
write unchanged. -/
theorem typedF_run (qt : Nat → EnvF) {Ft : Env} {a b : Nat} {F : List (Nat × Value)}
    {Gk : List Nat} (hab : a ≤ b) (hlen : b ≤ K.code.length) (hA : AbsSound A L g a b abs)
    (hF : Havoc.FactTags F Ft)
    (hc : checkF abs qt a b Ft Gk ((K.code.drop a).take (b - a)) = true)
    {t : TState} (ht : At t a F) (hq : QTF qt t) :
    ∃ u, run K A L g (b - a) t = some u ∧ At u b [] ∧ QTF qt u ∧
      (∀ k ∈ Gk, u.regs k = t.regs k) := by
  obtain ⟨hpc, hsub, hacc, hf, hH⟩ := ht
  unfold checkF at hc
  split at hc
  · cases hc
  rename_i e w hrun
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hq2, hk⟩ := hc
  have hq' : TypedF (qt a) t := by simpa [QTF, hpc] using hq
  have hT0 : TypedF (qt a ++ Ft.map fun p => (p.1, TagF.old p.2)) t := by
    intro r tg hl
    rcases lookup_append_some hl with h1 | ⟨-, h2⟩
    · exact hq' r tg h1
    · exact typedF_facts (Havoc.typed_facts hH hF) r tg h2
  obtain ⟨u, hu, hpcu, hsu, hau, hfu, htu, hfr⟩ :=
    crossF_aux hlen hA (b - a) a _ e w t le_rfl (by omega) hpc hsub hacc hf hT0 hrun
  refine ⟨u, hu, ⟨hpcu, hsu, hau, hfu, trivial⟩, ?_, fun k hk' => ?_⟩
  · unfold QTF
    rw [hpcu]
    intro r tg hr
    exact TagF.sat_ok (v := u.regs r) (need := tg) (h := e.lookup r)
      (by simpa using hq2 (r, tg) (lookup_mem' hr)) (fun tg' h' => htu r tg' h')
  · have hnk := hk k hk'
    simp only [Bool.not_eq_true'] at hnk
    exact hfr _ (by simpa using hnk)

/-- **A typed piece is a strict segment under the tag invariant.** -/
theorem segQF_of_typed (qt : Nat → EnvF) {Ft : Env} {a b : Nat} {F G : List (Nat × Value)}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hA : AbsSound A L g a b abs)
    (hF : Havoc.FactTags F Ft)
    (hc : checkF abs qt a b Ft (G.map Prod.fst) ((K.code.drop a).take (b - a)) = true)
    (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G := by
  intro t ht hq
  obtain ⟨u, hu, hAt, hQ, hk⟩ := typedF_run (K := K) (abs := abs) qt hab hlen hA hF hc ht hq
  refine ⟨u, run_rtg hu,
    ⟨hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, Havoc.holds_of_forall fun p hp => ?_⟩, hQ⟩
  rw [hk p.1 (List.mem_map_of_mem hp)]
  exact holds_mem ht.2.2.2.2 (hG p hp)

end PTX.Flow.TyG
