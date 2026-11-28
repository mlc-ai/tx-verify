-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQF
public import Lemmas.Flow.TypedFloatH

@[expose] public section

/-! # Typed runs with `min.f32` and `fma.rn.f32`, and single steps that need a fact of the lane

`absF2` is `absF` with the rule of `TypedFloatH.lean`; `segQF2_runW` is `segQF_runW` for it.
`SegQ.local1` is one local step whose success the caller shows from the state (an instruction whose
outcome needs a fact about the lane's own states, as an `add` without a rounding modifier: the
ideal rule does not decline), and `QTF.after1` keeps the tags across it. `TauAll R t` says `R`
holds of every state the local steps reach from `t`; a segment keeps it (`SegQ.tauAll`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The whole family of `TypedAllF.lean` and `TypedFloatH.lean`. -/
def absF2 (env : EnvF) (op : Op) : Option (List (Nat × TagF)) :=
  (absF env op).or (absFloat2 env op)

/-- What a kernel supplies for a stretch `[a, b)` of the family `absF2`. -/
structure FloatPlain2 (A : List Assumption) (L : Launch) (g a b : Nat) : Prop where
  plain : FloatPlain A L g a b
  ideal2 : IdealRules2 A L g a b

theorem FloatPlain2.mono {a b a' b' : Nat} (h : FloatPlain2 A L g a b) (h1 : a ≤ a')
    (h2 : b' ≤ b) : FloatPlain2 A L g a' b' where
  plain := h.plain.mono h1 h2
  ideal2 t ha hb := h.ideal2 t (le_trans h1 ha) (lt_of_lt_of_le hb h2)

theorem absF2_sound {a b : Nat} (h : FloatPlain2 A L g a b) : AbsSound A L g a b absF2 :=
  (absF_sound h.plain).or (absFloat2_sound h.ideal2)

/-- A typed run of the family `absF2` whose abstract run writes exactly `W`. -/
theorem segQF2_runW (qt : Nat → EnvF) {a b : Nat} {F G : List (Nat × Value)} {W : List Nat}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hP : FloatPlain2 A L g a b)
    (hc : checkW absF2 qt a b ((K.code.drop a).take (b - a)) W = true)
    (hw : ∀ p ∈ G, p.1 ∉ W) (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G := by
  obtain ⟨h0, hW⟩ := checkW_sound hc
  exact segQF_of_typed qt (Ft := []) hab hlen (absF2_sound hP) trivial
    (checkF_gk h0 fun k hk => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      exact hW ▸ hw p hp) hG

/-- `R` holds of every state the local steps reach from `t`. -/
def TauAll (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (R : TState → Prop)
    (t : TState) : Prop :=
  ∀ v, Relation.ReflTransGen (Tau K A L g) t v → R v

/-- A segment keeps `TauAll`. -/
theorem SegQ.tauAll {Q : TState → Prop} {a b : Nat} {F G : List (Nat × Value)}
    (R : TState → Prop) (h : SegQ K A L g Q a F b G) :
    SegQ K A L g (fun t => Q t ∧ TauAll K A L g R t) a F b G := by
  intro t ht ⟨hq, hf⟩
  obtain ⟨u, hr, hA, hQ⟩ := h t ht hq
  exact ⟨u, hr, hA, hQ, fun v hv => hf v (hr.trans hv)⟩

/-- A segment of `QTF` is a segment of `QTF` and `TauAll`, and the other way. -/
theorem SegQ.of_tauAll {Q : TState → Prop} {R : TState → Prop} {a b : Nat}
    {F G : List (Nat × Value)}
    (h : SegQ K A L g (fun t => Q t ∧ TauAll K A L g R t) a F b G) (hq : ∀ t, At t a F → Q t →
      TauAll K A L g R t) : SegQ K A L g Q a F b G := by
  intro t ht hQ
  obtain ⟨u, hr, hA, hQ', -⟩ := h t ht ⟨hQ, hq t ht hQ⟩
  exact ⟨u, hr, hA, hQ'⟩

/-- **One local instruction** whose step the caller shows succeeds from the state. -/
theorem SegQ.local1 {Q : TState → Prop} {pc : Nat} {op : Op} {F G : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hG : ∀ p ∈ G, p ∈ F)
    (hs : ∀ t, At t pc F → Q t → ∃ u, execLocalA A L g t op = .ok u ∧ u.pc = pc + 1 ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault ∧ (∀ p ∈ G, u.regs p.1 = t.regs p.1) ∧
      (Tau K A L g t u → Q u)) : SegQ K A L g Q pc F (pc + 1) G := by
  intro t ht hq
  obtain ⟨u, hex, hpc, hsub, hacc, hf, hfr, hQ⟩ := hs t ht hq
  have htau := tau_of_ok (A := A) (L := L) (g := g) (by rw [ht.1]; exact hc) hl ht.2.2.2.1 hex
  refine ⟨u, .single htau, ⟨hpc, hsub.trans ht.2.1, hacc.trans ht.2.2.1,
    hf.trans ht.2.2.2.1, Havoc.holds_of_forall fun p hp => ?_⟩, hQ htau⟩
  rw [hfr p hp]
  exact holds_mem ht.2.2.2.2 (hG p hp)

/-- The tags at `pc + 1` are those of the registers a step writes or already held at `pc`. -/
def afterF (qt : Nat → EnvF) (pc : Nat) (outs : List (Nat × TagF)) : Bool :=
  (qt (pc + 1)).all fun p => TagF.sat ((outs ++ qt pc).lookup p.1) p.2

theorem QTF.after1 {qt : Nat → EnvF} {t u : TState} {pc : Nat} {outs : List (Nat × TagF)}
    (ht : QTF qt t) (hpc : t.pc = pc) (hu : u.pc = pc + 1)
    (hw : ∀ r, r ∉ outs.map Prod.fst → u.regs r = t.regs r)
    (hv : ∀ p ∈ outs, p.2.ok (u.regs p.1)) (h : afterF qt pc outs = true) : QTF qt u := by
  have ht' : TypedF (qt pc) t := by simpa [QTF, hpc] using ht
  have hty := typedF_cons ht' hw hv
  unfold QTF
  rw [hu]
  intro r tg hr
  simp only [afterF, List.all_eq_true] at h
  exact TagF.sat_ok (v := u.regs r) (need := tg) (h := (outs ++ qt pc).lookup r)
    (by simpa using h (r, tg) (lookup_mem' hr)) (fun tg' h' => hty r tg' h')

end PTX.Flow.TyG
