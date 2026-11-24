-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PackMul
public import Lemmas.Flow.FloatRun

@[expose] public section

/-! # Pieces that continue under a condition and kill the thread otherwise

A proof tool, for local segments that read values a site machine does not constrain (raw words
a load returned). `SegD … C` is a piece (`Seg`) under the condition `C`, and without `C` the
thread is dead: its local steps reach undefined behaviour. Pieces compose (`SegD.comp`), the
conditions conjoined; a piece without condition is a `Seg` (`SegD.of_seg`). A run of packs is
such a piece (`SegD.packs`): it continues when every source word has four bytes.

Deadness propagates back along local steps (`dead_of_rtg`, `dead_of_run`), and a local
instruction whose step fails kills the thread (`dead_of_error`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A state from which local steps reach a dead state is dead. -/
theorem dead_of_rtg {t t1 : TState} (h : Relation.ReflTransGen (Tau K A L g) t t1)
    (hd : Machine.Dead (K := K) (A := A) (L := L) (g := g) t1) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  obtain ⟨s, f, hs, hf⟩ := hd
  exact ⟨s, f, h.trans hs, hf⟩

/-- A state whose local run reaches a dead state is dead. -/
theorem dead_of_run {n : Nat} {t t1 : TState} (h : run K A L g n t = some t1)
    (hd : Machine.Dead (K := K) (A := A) (L := L) (g := g) t1) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t :=
  dead_of_rtg (run_rtg h) hd

/-- A local instruction whose step fails kills the thread. -/
theorem dead_of_error {t : TState} {op : Op} {f : Fault}
    (hc : K.code[t.pc]? = some ⟨none, op⟩) (hl : op.isLocal = true) (hf : t.fault = none)
    (he : execLocalA A L g t op = .error f) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t :=
  Machine.dead_of_ub (f := f) (by simp [out, hf, hc, guardHolds, hl, he, pure, Except.pure])

/-- A local instruction whose step succeeds is one local step. -/
theorem tau_of_ok {t t1 : TState} {op : Op} (hc : K.code[t.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (hf : t.fault = none) (he : execLocalA A L g t op = .ok t1) :
    out K A L g t = .tau t1 := by
  simp [out, hf, hc, guardHolds, hl, he, pure, Except.pure]

/-- From every state at `s` with facts `F`: under `C`, `n` local steps reach a state at `b`
with facts `G`; without `C` the thread is dead. -/
def SegD (K : Kernel) (A : List Assumption) (L : Launch) (g n s : Nat)
    (F : List (Nat × Value)) (b : Nat) (G : List (Nat × Value)) (C : Prop) : Prop :=
  ∀ t, At t s F → (C → ∃ t', run K A L g n t = some t' ∧ At t' b G) ∧
    (¬ C → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)

namespace SegD

/-- A piece without condition. -/
theorem of_seg {n s b : Nat} {F G : List (Nat × Value)} (h : Seg K A L g n s F b G) :
    SegD K A L g n s F b G True :=
  fun t ht => ⟨fun _ => h t ht, fun hc => absurd trivial hc⟩

/-- Two pieces that meet at a checkpoint, under both conditions. -/
theorem comp {m n s p b : Nat} {F G H : List (Nat × Value)} {C₁ C₂ : Prop}
    (h1 : SegD K A L g m s F p G C₁) (h2 : SegD K A L g n p G b H C₂) :
    SegD K A L g (m + n) s F b H (C₁ ∧ C₂) := by
  intro t ht
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨t1, hr1, h1'⟩ := (h1 t ht).1 hc.1
    obtain ⟨t2, hr2, h2'⟩ := (h2 t1 h1').1 hc.2
    exact ⟨t2, run_comp hr1 hr2, h2'⟩
  · by_cases hc1 : C₁
    · obtain ⟨t1, hr1, h1'⟩ := (h1 t ht).1 hc1
      exact dead_of_run hr1 ((h2 t1 h1').2 fun hc2 => hc ⟨hc1, hc2⟩)
    · exact (h1 t ht).2 hc1

/-- The same piece under an equivalent condition. -/
theorem iff {n s b : Nat} {F G : List (Nat × Value)} {C C' : Prop}
    (h : SegD K A L g n s F b G C) (hC : C ↔ C') : SegD K A L g n s F b G C' :=
  fun t ht => ⟨fun hc => (h t ht).1 (hC.mpr hc), fun hc => (h t ht).2 (fun h' => hc (hC.mp h'))⟩

/-- The same piece with its length written differently. -/
theorem of_len {m n s b : Nat} {F G : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g m s F b G C) (hmn : m = n) : SegD K A L g n s F b G C :=
  hmn ▸ h

/-- Fewer or restated facts at the end. -/
theorem weaken_end {n s b : Nat} {F G G' : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g n s F b G C) (hG : ∀ R, Holds R G → Holds R G') :
    SegD K A L g n s F b G' C := by
  intro t ht
  refine ⟨fun hc => ?_, (h t ht).2⟩
  obtain ⟨t', hr, h'⟩ := (h t ht).1 hc
  exact ⟨t', hr, At.mono h' (hG _ h'.2.2.2.2)⟩

/-- More or restated facts at the start. -/
theorem weaken_start {n s b : Nat} {F F' G : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g n s F b G C) (hF : ∀ R, Holds R F' → Holds R F) :
    SegD K A L g n s F' b G C :=
  fun t ht => h t (At.mono ht (hF _ ht.2.2.2.2))

/-- Under the condition, a piece. -/
theorem seg {n s b : Nat} {F G : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g n s F b G C) (hc : C) : Seg K A L g n s F b G :=
  fun t ht => (h t ht).1 hc

end SegD

/-- A value `lookup` finds is in the list. -/
theorem mem_of_lookup {ys : List (Nat × Value)} {r : Nat} {v : Value}
    (h : ys.lookup r = some v) : (r, v) ∈ ys := by
  induction ys with
  | nil => cases h
  | cons p ys ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      simp [eq_of_beq hk]
    · exact List.mem_cons_of_mem _ (ih h)

/-- Explicit values that agree with the table change nothing. -/
theorem valueEx_agree {base : Nat → Value} {ys : List (Nat × Value)}
    (h : ys.map (fun p => base p.1) = ys.map Prod.snd) : valueEx base ys = base := by
  funext r
  unfold valueEx
  cases hl : ys.lookup r with
  | none => rfl
  | some v =>
    have hm := mem_of_lookup hl
    have := List.map_inj_left.mp h _ hm
    simpa using this.symm

/-- Explicit values behind others that agree with the table change nothing. -/
theorem valueEx_append_agree {base : Nat → Value} {ys zs : List (Nat × Value)}
    (h : zs.map (fun p => base p.1) = zs.map Prod.snd) :
    valueEx base (ys ++ zs) = valueEx base ys := by
  funext r
  have hz := congrFun (valueEx_agree h) r
  unfold valueEx at hz ⊢
  cases hl : ys.lookup r with
  | some v => rw [lookup_append_some hl]
  | none =>
    have hk : r ∉ ys.map Prod.fst := fun hk => by
      obtain ⟨v, hv⟩ := lookup_of_mem_keys hk
      rw [hv] at hl; cases hl
    rw [lookup_append_none hk]
    exact hz

/-- Facts with explicit values that agree with the table are the table's facts. -/
theorem holds_agree {R : Nat → Option Value} {live : List Nat} {base : Nat → Value}
    {ys : List (Nat × Value)} (h : ys.map (fun p => base p.1) = ys.map Prod.snd)
    (hR : Holds R (factsFrom live (valueEx base ys))) : Holds R (factsFrom live base) := by
  rwa [valueEx_agree h] at hR

/-- Explicit values behind others that agree with the table can be dropped from facts. -/
theorem holds_append_agree {R : Nat → Option Value} {live : List Nat} {base : Nat → Value}
    {ys zs : List (Nat × Value)} (h : zs.map (fun p => base p.1) = zs.map Prod.snd)
    (hR : Holds R (factsFrom live (valueEx base (ys ++ zs)))) :
    Holds R (factsFrom live (valueEx base ys)) := by
  rwa [valueEx_append_agree h] at hR

/-! ### A run of packs -/

/-- The packs' destinations with their joined pairs, the last pack first. -/
def packVals (v : Nat → Value) : List (Nat × Nat × Nat) → List (Nat × Value)
  | [] => []
  | p :: ps => packVals v ps ++ [(p.1, joinValue (v p.2.1) (v p.2.2))]

theorem packVals_keys (v : Nat → Value) {r : Nat} :
    ∀ ps : List (Nat × Nat × Nat), r ∈ (packVals v ps).map Prod.fst ↔ r ∈ ps.map Prod.fst
  | [] => by simp [packVals]
  | p :: ps => by
    simp only [packVals, List.map_append, List.mem_append, packVals_keys v ps, List.map_cons,
      List.mem_cons, List.map_nil]
    tauto

theorem packVals_lookup (v : Nat → Value) {r : Nat} : ∀ (ps : List (Nat × Nat × Nat)),
    (ps.map Prod.fst).Nodup → ∀ p ∈ ps, p.1 = r →
      (packVals v ps).lookup r = some (joinValue (v p.2.1) (v p.2.2))
  | [], _, _, hp, _ => by simp at hp
  | q :: ps, hnd, p, hp, hr => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [packVals]
    rcases List.mem_cons.mp hp with rfl | hp
    · subst hr
      rw [lookup_append_none (fun h => hnd.1 ((packVals_keys v ps).mp h))]
      simp [List.lookup]
    · exact lookup_append_some (packVals_lookup v ps hnd.2 p hp hr)

/-- **A run of packs, as a piece**: from facts with explicit values, the joined pairs in front,
when every source word has four bytes; otherwise the thread is dead. No assumption of `A` names
the packs (`hN`), since the local step consults the assumptions before the Core rule. -/
theorem SegD.packs {pc : Nat} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} {ps : List (Nat × Nat × Nat)} (hN : NoPack A)
    (hcode : packCodeB K pc ps = true)
    (hreads : ∀ p ∈ ps, p.2.1 ∈ liveS ∧ p.2.2 ∈ liveS)
    (hdis : ∀ p ∈ ps, ∀ q ∈ ps, q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2) (hnd : (ps.map Prod.fst).Nodup)
    (hS : ∀ i < ps.length, Assumption.SegFreePc A (pc + i))
    (hcov : ∀ r ∈ liveT, r ∈ ps.map Prod.fst ∨ (r ∉ ps.map Prod.fst ∧ r ∈ liveS)) :
    SegD K A L g ps.length pc (factsFrom liveS (valueEx base ex)) (pc + ps.length)
      (factsFrom liveT (valueEx base (packVals (valueEx base ex) ps ++ ex)))
      (packsOk (valueEx base ex) ps = true) := by
  intro t h
  have hR := h.2.2.2.2
  have hrun := packs_run (K := K) (A := A) (L := L) (g := g) hN (valueEx base ex) ps t
    (PackCode.of_bool (h.1 ▸ hcode)) h.2.2.2.1
    (fun p hp => ⟨holds_mem hR (mem_factsFrom (hreads p hp).1),
      holds_mem hR (mem_factsFrom (hreads p hp).2)⟩) hdis (fun i hi => h.1 ▸ hS i hi)
  refine ⟨fun hc => ?_, fun hc => hrun.2 (by simpa using hc)⟩
  obtain ⟨h1, h2, h3, h4⟩ := packRun_skel (valueEx base ex) ps t
  refine ⟨_, hrun.1 hc, by rw [h1, h.1], h2.trans h.2.1, h3.trans h.2.2.1, h4.trans h.2.2.2.1,
    ?_⟩
  refine holds_ext (W := ps.map Prod.fst) hR
    (fun r hr => packRun_other _ ps t (fun p hp he => hr (List.mem_map.mpr ⟨p, hp, he⟩)))
    (fun r hr => ?_) (fun r hr => ?_)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((packVals_keys _ ps).mp hr)
    rw [packVals_lookup _ ps hnd p hp rfl]
    exact packRun_val _ ps t hnd (by simpa using hp)
  · rcases hcov r hr with h1 | h2
    · exact .inl ((packVals_keys _ ps).mpr h1)
    · exact .inr h2

end
end PTX.Flow
