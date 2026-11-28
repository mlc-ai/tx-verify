-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedAllF
public import Lemmas.Flow.SegQOps

@[expose] public section

/-! # Typed runs and branches under the float-tag invariant

The pieces a generated window is made of. `segQF_run` is `segQF_of_typed` with the abstract rule
`absF` and no value facts: a stretch whose abstract run accepts it is a strict segment from facts
`F` to facts `G ⊆ F` that it does not write, under the invariant `QTF qt`. `SegQF.bra` follows a
segment with a guarded branch whose predicate is assumed to read `pick` (a fact of the control
machine that the typed run cannot derive): the segment continues at the target or at the next
pc, the tags of that pc among those of the branch's. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem memL {x : Nat} {l m : List Nat} (h : x ∈ l) : x ∈ l ++ m := List.mem_append_left _ h

theorem memR {x : Nat} {l m : List Nat} (h : x ∈ m) : x ∈ l ++ m := List.mem_append_right _ h

/-- The tags `e'` are among the tags `e`. -/
def tagsInF (e' e : EnvF) : Bool := e'.all fun p => e.lookup p.1 == some p.2

theorem typedF_of_tagsIn {e e' : EnvF} {t : TState} (h : tagsInF e' e = true)
    (ht : TypedF e t) : TypedF e' t := by
  intro r tg hr
  simp only [tagsInF, List.all_eq_true, beq_iff_eq] at h
  exact ht r tg (h _ (lookup_mem' hr))

/-- The registers an abstract run writes. -/
def wrF (abs : EnvF → Op → Option (List (Nat × TagF))) (env : EnvF) (ops : List Instr) :
    List Nat :=
  match runF abs env ops with
  | some (_, w) => w
  | none => []

/-- The check with the registers the run writes stated: one evaluation gives both. -/
def checkW (abs : EnvF → Op → Option (List (Nat × TagF))) (qt : Nat → EnvF) (a b : Nat)
    (ops : List Instr) (W : List Nat) : Bool :=
  match runF abs (qt a) ops with
  | none => false
  | some (e, w) => (qt b).all (fun p => TagF.sat (e.lookup p.1) p.2) && decide (w = W)

theorem checkW_sound {abs : EnvF → Op → Option (List (Nat × TagF))} {qt : Nat → EnvF}
    {a b : Nat} {ops : List Instr} {W : List Nat} (h : checkW abs qt a b ops W = true) :
    checkF abs qt a b [] [] ops = true ∧ wrF abs (qt a) ops = W := by
  unfold checkW at h
  unfold checkF wrF
  cases hr : runF abs (qt a) ops with
  | none => simp [hr] at h
  | some r =>
    obtain ⟨e, w⟩ := r
    simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_nil, List.append_nil, hr, List.all_nil, Bool.and_true]
    exact ⟨h.1, h.2⟩

/-- The check without registers to keep, and the registers the run writes, give the check. -/
theorem checkF_gk {abs : EnvF → Op → Option (List (Nat × TagF))} {qt : Nat → EnvF} {a b : Nat}
    {Gk : List Nat} {ops : List Instr}
    (h0 : checkF abs qt a b [] [] ops = true) (hw : ∀ k ∈ Gk, k ∉ wrF abs (qt a) ops) :
    checkF abs qt a b [] Gk ops = true := by
  unfold checkF at h0 ⊢
  simp only [List.map_nil, List.append_nil] at h0 ⊢
  unfold wrF at hw
  cases hr : runF abs (qt a) ops with
  | none => simp [hr] at h0
  | some r =>
    obtain ⟨e, w⟩ := r
    simp only [hr, Bool.and_eq_true, List.all_nil, Bool.and_true] at h0 ⊢
    simp only [hr] at hw
    refine ⟨h0, ?_⟩
    simp only [List.all_eq_true, Bool.not_eq_true']
    intro k hk
    simpa using hw k hk

theorem FloatPlain.mono {a b a' b' : Nat} (h : FloatPlain A L g a b) (h1 : a ≤ a') (h2 : b' ≤ b) :
    FloatPlain A L g a' b' where
  shape t ha hb := h.shape t (le_trans h1 ha) (lt_of_lt_of_le hb h2)
  segs pc ha hb := h.segs pc (le_trans h1 ha) (lt_of_lt_of_le hb h2)
  ideal t ha hb := h.ideal t (le_trans h1 ha) (lt_of_lt_of_le hb h2)
  widen t ha hb := h.widen t (le_trans h1 ha) (lt_of_lt_of_le hb h2)
  bra := h.bra

/-- **A typed run is a strict segment** under the float-tag invariant, from facts `F` to the
facts `G` of `F` that the run does not write. -/
theorem segQF_run (qt : Nat → EnvF) {a b : Nat} {F G : List (Nat × Value)} (hab : a ≤ b)
    (hlen : b ≤ K.code.length) (hP : FloatPlain A L g a b)
    (h0 : checkF absF qt a b [] [] ((K.code.drop a).take (b - a)) = true)
    (hw : ∀ p ∈ G, p.1 ∉ wrF absF (qt a) ((K.code.drop a).take (b - a)))
    (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G :=
  segQF_of_typed qt (Ft := []) hab hlen (absF_sound hP) trivial
    (checkF_gk h0 fun k hk => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      exact hw p hp) hG

/-- A typed run whose abstract run writes exactly the registers `W`. -/
theorem segQF_runW (qt : Nat → EnvF) {a b : Nat} {F G : List (Nat × Value)} {W : List Nat}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hP : FloatPlain A L g a b)
    (hc : checkW absF qt a b ((K.code.drop a).take (b - a)) W = true)
    (hw : ∀ p ∈ G, p.1 ∉ W) (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G := by
  obtain ⟨h0, hW⟩ := checkW_sound hc
  exact segQF_run qt hab hlen hP h0 (fun p hp => hW ▸ hw p hp) hG

/-- **A guarded branch** after a strict segment: the predicate is assumed to read `pick`, and the
segment goes on at the target or at the next pc, whose tags are among those at the branch. -/
theorem SegQF.bra {qt : Nat → EnvF} {a pc p target : Nat} {uni : Bool} {F G : List (Nat × Value)}
    (pick : Bool) (h1 : SegQ K A L g (QTF qt) a F pc G)
    (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hL : ∀ t x, x ∈ A → x.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsInF (qt (if pick then target else pc + 1)) (qt pc) = true)
    (hp : ∀ u, At u pc G → QTF qt u → u.regs p = some (.pred pick)) :
    SegQ K A L g (QTF qt) a F (if pick then target else pc + 1) G := by
  intro t ht hq0
  obtain ⟨u, hr, hu, hQ⟩ := h1 t ht hq0
  obtain ⟨v, hl, hregs, hv⟩ := run_bra_regs hc pick hu (hp u hu hQ) (hL u) hA
  refine ⟨v, hr.trans (run_rtg hl), hv, ?_⟩
  have hQ' : TypedF (qt pc) u := by simpa [QTF, hu.1] using hQ
  have : TypedF (qt (if pick then target else pc + 1)) v := by
    intro r tg hr'
    rw [hregs]
    exact typedF_of_tagsIn hq hQ' r tg hr'
  simpa [QTF, hv.1] using this

end PTX.Flow.TyG
