-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Havoc
public import Lemmas.Flow.TypedOps
public import Lemmas.Flow.SegQ
public import Lemmas.Snoc.ControlEffect

@[expose] public section

/-! # A typed crossing of a stretch that cannot fail

`Havoc.cross` crosses a stretch of local instructions whose results nobody reads and allows the
thread to die on the way (`Machine.Dead`), because it knows nothing of the registers' values.
`crossT` crosses a stretch given the *tags* of the registers it reads (`Lemmas/Flow/TypedOps.lean`):
the abstract run `runT` follows the stretch instruction by instruction, each of which must be a
plain integer, move or conversion that cannot fail on registers of its sources' tags, and ends with
the tags of every register it wrote. The thread then reaches the stretch's end, without a dead
alternative, in a state of those tags, with every register the stretch did not write unchanged.

`SegQ.of_typed` states it as a strict segment under the invariant "the registers have the tags
`qt pc`" (`QTyped`), whose tags at the end are those of the run, or of the facts. -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The abstract run of a decoded stretch: the tags after it, if every instruction is a plain
guard-free local one that cannot fail on the tags before it. -/
def runT (env : Env) : List Instr → Option Env
  | [] => some env
  | ins :: rest =>
    if ins.guard.isNone && ins.op.isLocal then
      (absOp env ins.op).bind fun p => runT (p :: env) rest
    else none

/-- The registers a stretch writes. -/
def wrT (ops : List Instr) : List Nat := ops.flatMap fun ins => writesRegs ins.op

/-- No assumption's local rule takes an instruction of the stretch `[a, b)` that the abstract run
accepts. -/
def PlainRules (A : List Assumption) (L : Launch) (g a b : Nat) : Prop :=
  ∀ t : TState, a ≤ t.pc → t.pc < b → ∀ op : Op, (∃ env, (absOp env op).isSome) →
    ∀ x ∈ A, x.localRule L g t op = none

/-- The stretch `[a, b)` is free of assumption segments. -/
def PlainSegs (A : List Assumption) (a b : Nat) : Prop :=
  ∀ pc, a ≤ pc → pc < b → Assumption.SegFreePc A pc

theorem take_cons {code : List Instr} {pc n : Nat} (h : pc < code.length) :
    (code.drop pc).take (n + 1) = code[pc] :: (code.drop (pc + 1)).take n := by
  rw [List.drop_eq_getElem_cons h]
  rfl

/-- **The crossing**: from a state at `pc` with the tags `env`, the stretch of `n` instructions
up to `b = pc + n` ends at `b` with the tags of its abstract run. -/
theorem crossT_aux {a b : Nat} (hlen : b ≤ K.code.length) (hN : PlainRules A L g a b)
    (hS : PlainSegs A a b) :
    ∀ (n pc : Nat) (env env' : Env) (t : TState), a ≤ pc → pc + n = b → t.pc = pc →
      t.sub = 0 → t.acc = [] → t.fault = none → Typed env t →
      runT env ((K.code.drop pc).take n) = some env' →
      ∃ u, run K A L g n t = some u ∧ u.pc = b ∧ u.sub = 0 ∧ u.acc = [] ∧
        u.fault = none ∧ Typed env' u ∧
        ∀ r, r ∉ wrT ((K.code.drop pc).take n) → u.regs r = t.regs r := by
  intro n
  induction n with
  | zero =>
    intro pc env env' t _ hb hpc hsub hacc hf ht hr
    simp only [List.take_zero, runT, Option.some.injEq] at hr
    subst hr
    exact ⟨t, rfl, by omega, hsub, hacc, hf, ht, fun _ _ => rfl⟩
  | succ n ih =>
    intro pc env env' t ha hb hpc hsub hacc hf ht hr
    have hlt : pc < K.code.length := by omega
    rw [take_cons hlt] at hr ⊢
    simp only [runT, Bool.and_eq_true] at hr
    split_ifs at hr with hg
    obtain ⟨hguard, hl⟩ := hg
    obtain ⟨⟨d, tg⟩, hab, hr2⟩ := Option.bind_eq_some_iff.mp hr
    have hcode : K.code[pc]? = some ⟨none, K.code[pc].op⟩ := by
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq]
      have hg := Option.isNone_iff_eq_none.mp hguard
      generalize K.code[pc] = ins at hg ⊢
      rcases ins with ⟨gd, op⟩
      simp only at hg
      rw [hg]
    obtain ⟨v, hv, hok⟩ := exec_of_abs (L := L) (g := g) hab ht
    have hpc' : a ≤ t.pc ∧ t.pc < b := ⟨hpc ▸ ha, by omega⟩
    have hNo := hN t hpc'.1 hpc'.2 K.code[pc].op ⟨env, by simp [hab]⟩
    have hex : execLocalA A L g t K.code[pc].op = .ok (next (setReg t d v)) := by
      rw [execLocalA_noOverride hNo (by rw [hpc]; exact hS pc ha (by omega))]
      exact hv
    have htau := tau_of_ok (A := A) (L := L) (g := g) (by rw [hpc]; exact hcode) hl hf hex
    have hty := typed_set (d := d) (tg := tg) ht hok
    obtain ⟨u, hu, hpcu, hsu, hau, hfu, htu, hfr⟩ :=
      ih (pc + 1) ((d, tg) :: env) env' (next (setReg t d v)) (by omega) (by omega)
        (by simp [next, setReg, hpc]) (by simpa [next, setReg] using hsub)
        (by simpa [next, setReg] using hacc) (by simpa [next, setReg] using hf) hty hr2
    refine ⟨u, ?_, hpcu, hsu, hau, hfu, htu, fun r hr' => ?_⟩
    · show (tauStep K A L g t).bind (run K A L g n) = some u
      rw [tauStep_iff.mpr htau]
      exact hu
    simp only [wrT, List.flatMap_cons, List.mem_append, not_or] at hr' ⊢
    rw [hfr r (by simpa [wrT] using hr'.2)]
    have hd : writesRegs K.code[pc].op = [d] := writes_of_abs hab
    rw [hd] at hr'
    simp only [next, setReg]
    exact Function.update_of_ne (by simpa using hr'.1) _ _

/-- The tag of a fact's value, when a local instruction can read it. -/
def tagOf : Value → Option Tag
  | .bits w _ => some (.bits w)
  | .pred _ => some .pred
  | _ => none

/-- The tags `Ft` are those of facts of `F`. -/
def FactTags (F : List (Nat × Value)) : Env → Prop
  | [] => True
  | (r, tg) :: rest => (match F.lookup r with
    | some v => tagOf v = some tg
    | none => False) ∧ FactTags F rest

/-- The tag `have` serves a use that needs `need`. -/
def Tag.sat : Option Tag → Tag → Bool
  | some (.bits w), .bits v | some (.nz w), .bits v | some (.nz w), .nz v => w == v
  | some .pred, .pred => true
  | _, _ => false

theorem Tag.sat_ok {h : Option Tag} {need : Tag} {v : Option Value} (hs : Tag.sat h need = true)
    (hh : ∀ tg, h = some tg → tg.ok v) : need.ok v := by
  cases h with
  | none => simp [Tag.sat] at hs
  | some tg =>
    have := hh tg rfl
    cases tg <;> cases need <;> simp only [Tag.sat, Bool.false_eq_true, beq_iff_eq] at hs <;>
      simp only [Tag.ok] at this ⊢
    · subst hs; exact this
    · subst hs; obtain ⟨x, hx, -⟩ := this; exact ⟨x, hx⟩
    · subst hs; exact this
    · exact this

theorem lookup_mem : ∀ {l : Env} {r : Nat} {tg : Tag}, l.lookup r = some tg → (r, tg) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (r0, t0) :: ps, r, tg, h => by
    by_cases hr : (r == r0) = true
    · simp only [List.lookup, hr] at h
      obtain rfl := beq_iff_eq.mp hr
      obtain rfl := Option.some.inj h
      simp
    · have hr' : (r == r0) = false := by simpa using hr
      simp only [List.lookup, hr'] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_append {e1 e2 : Env} {r : Nat} {tg : Tag} (h : (e1 ++ e2).lookup r = some tg) :
    e1.lookup r = some tg ∨ (e1.lookup r = none ∧ e2.lookup r = some tg) := by
  induction e1 with
  | nil => exact .inr ⟨rfl, h⟩
  | cons p ps ih =>
    by_cases hr : (r == p.1) = true
    · simp only [List.cons_append, List.lookup, hr] at h
      simp only [List.lookup, hr]
      exact .inl h
    · have hr' : (r == p.1) = false := by simpa using hr
      simp only [List.cons_append, List.lookup, hr'] at h
      simp only [List.lookup, hr']
      exact ih h

theorem typed_append {e1 e2 : Env} {t : TState} (h1 : Typed e1 t) (h2 : Typed e2 t) :
    Typed (e1 ++ e2) t := by
  intro r tg h
  rcases lookup_append h with h | ⟨-, h⟩
  · exact h1 r tg h
  · exact h2 r tg h

theorem typed_facts {F : List (Nat × Value)} {Ft : Env} {t : TState} (hF : Holds t.regs F)
    (hT : FactTags F Ft) : Typed Ft t := by
  induction Ft with
  | nil => intro r tg h; simp [List.lookup] at h
  | cons p ps ih =>
    obtain ⟨r0, tg0⟩ := p
    obtain ⟨hp, hps⟩ := hT
    intro r tg h
    by_cases hr : (r == r0) = true
    · simp only [List.lookup, hr] at h
      obtain rfl := Option.some.inj h
      obtain rfl := beq_iff_eq.mp hr
      cases hl : F.lookup r with
      | none => simp [hl] at hp
      | some v =>
        simp only [hl] at hp
        have hm := holds_lookup hF hl
        cases v <;> simp only [tagOf, Option.some.injEq, reduceCtorEq] at hp
        · subst hp; exact ⟨_, hm⟩
        · subst hp; exact ⟨_, hm⟩
    · have hr' : (r == r0) = false := by simpa using hr
      simp only [List.lookup, hr'] at h
      exact ih hps r tg h

/-- The tags an invariant `qt` asks of the registers at a program counter. -/
def QT (qt : Nat → Env) (t : TState) : Prop := Typed (qt t.pc) t

/-- The check of a typed piece from `a` to `b`: the abstract run of its instructions from the
tags `qt a` and those of the facts `Ft` ends with the tags `qt b` asks for, and writes none of the
registers `Gk`. -/
def checkQ (qt : Nat → Env) (a b : Nat) (Ft : Env) (Gk : List Nat) (ops : List Instr) : Bool :=
  match runT (qt a ++ Ft) ops with
  | none => false
  | some e => (qt b).all (fun p => Tag.sat (e.lookup p.1) p.2) &&
      Gk.all (fun k => !(wrT ops).contains k)

theorem holds_of_forall {R : Nat → Option Value} {G : List (Nat × Value)}
    (h : ∀ p ∈ G, R p.1 = some p.2) : Holds R G := by
  induction G with
  | nil => trivial
  | cons p ps ih => exact ⟨h p List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- **A typed piece runs**: from a state of the tags `qt a` and the facts `F`, the piece's
`b - a` local steps end at `b` in a state of the tags `qt b`, the registers the stretch does not
write unchanged. -/
theorem typed_run (qt : Nat → Env) {Ft : Env} {a b : Nat} {F : List (Nat × Value)} {Gk : List Nat}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hN : PlainRules A L g a b) (hS : PlainSegs A a b)
    (hF : FactTags F Ft)
    (hc : checkQ qt a b Ft Gk ((K.code.drop a).take (b - a)) = true)
    {t : TState} (ht : At t a F) (hq : QT qt t) :
    ∃ u, run K A L g (b - a) t = some u ∧ At u b [] ∧ QT qt u ∧
      (∀ k ∈ Gk, u.regs k = t.regs k) := by
  obtain ⟨hpc, hsub, hacc, hf, hH⟩ := ht
  unfold checkQ at hc
  split at hc
  · cases hc
  rename_i e hrun
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hq2, hk⟩ := hc
  have hq' : Typed (qt a) t := by simpa [QT, hpc] using hq
  have hT0 : Typed (qt a ++ Ft) t := typed_append hq' (typed_facts hH hF)
  obtain ⟨u, hu, hpcu, hsu, hau, hfu, htu, hfr⟩ :=
    crossT_aux hlen hN hS (b - a) a (qt a ++ Ft) e t le_rfl (by omega) hpc hsub hacc hf hT0 hrun
  refine ⟨u, hu, ⟨hpcu, hsu, hau, hfu, trivial⟩, ?_, fun k hk' => ?_⟩
  · unfold QT
    rw [hpcu]
    intro r tg hr
    have hr' := lookup_mem hr
    have := Tag.sat_ok (v := u.regs r) (need := tg) (h := e.lookup r)
      (by simpa using hq2 (r, tg) hr') (fun tg' h' => htu r tg' h')
    exact this
  · have hnk := hk k hk'
    simp only [Bool.not_eq_true'] at hnk
    exact hfr _ (by simpa using hnk)

/-- **A typed piece is a strict segment under the tag invariant.** The stretch from `a` to `b`
cannot fail on registers of the tags `qt a` and those of the facts `F` (`Ft`), reaches `b` in a
state of the tags `qt b`, and the facts `G` (among `F`) survive it. -/
theorem SegQ.of_typed (qt : Nat → Env) {Ft : Env} {a b : Nat} {F G : List (Nat × Value)}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hN : PlainRules A L g a b) (hS : PlainSegs A a b)
    (hF : FactTags F Ft)
    (hc : checkQ qt a b Ft (G.map Prod.fst) ((K.code.drop a).take (b - a)) = true)
    (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QT qt) a F b G := by
  intro t ht hq
  obtain ⟨u, hu, hAt, hQ, hk⟩ := typed_run qt hab hlen hN hS hF hc ht hq
  refine ⟨u, run_rtg hu,
    ⟨hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, holds_of_forall fun p hp => ?_⟩, hQ⟩
  rw [hk p.1 (List.mem_map_of_mem hp)]
  exact holds_mem ht.2.2.2.2 (hG p hp)

/-- **An exact piece under the tag invariant**: a strict segment (`Seg`) whose stretch also passes
the typed check (so the tags `qt b` hold at its end). -/
theorem SegQ.of_seg_typed (qt : Nat → Env) {Ft : Env} {a b n : Nat} {F G : List (Nat × Value)}
    (hseg : Seg K A L g n a F b G) (hn : n = b - a) (hab : a ≤ b)
    (hlen : b ≤ K.code.length) (hN : PlainRules A L g a b) (hS : PlainSegs A a b)
    (hF : FactTags F Ft) (hc : checkQ qt a b Ft [] ((K.code.drop a).take (b - a)) = true) :
    SegQ K A L g (QT qt) a F b G := by
  intro t ht hq
  obtain ⟨u, hu, -, hQ, -⟩ := typed_run qt hab hlen hN hS hF hc ht hq
  obtain ⟨u2, hu2, hAt⟩ := hseg t ht
  subst hn
  rw [hu] at hu2
  obtain rfl := Option.some.inj hu2
  exact ⟨u, run_rtg hu, hAt, hQ⟩

end PTX.Flow.Havoc
