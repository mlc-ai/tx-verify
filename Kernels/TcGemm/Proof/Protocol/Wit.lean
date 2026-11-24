-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Trace

@[expose] public section

/-! # `tc_gemm`: every thread's trace is a prefix of its whole trace

From the thread facts: before each state the events of a thread are a prefix of its whole trace
`fullE P` (`along_form`), and a thread whose machine stopped did so at a read whose bytes give
no column (followed by at most its undefined behaviour), at the undefined behaviour of a store, or
at the exit (`thread_form`). So an execution is described by the values `P g` each thread's events
returned, the length `m g` of its prefix of `fullE (P g)` and its undefined behaviour `u g`
(`Wit`, `wit`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- An execution, thread by thread: a prefix of the whole trace for the values the thread's events
returned, then possibly one undefined-behaviour event. -/
structure Wit (A B D S : Nat) (X : Execution) (P : Nat → Par) (m : Nat → Nat)
    (u : Nat → List Event) : Prop where
  tr : ∀ g < 128, X.tr g = (fullE A B D S g (P g)).take (m g) ++ u g
  len : ∀ g < 128, m g ≤ (fullE A B D S g (P g)).length
  rd : ∀ g, (P g).rd.length = 4
  vals : ∀ g, (P g).vals.length = 8
  col : ∀ g, (P g).col < 2 ^ 16
  /-- Past the read, its bytes give the column. -/
  good : ∀ g < 128, hd g + 1 < m g → rdCol (P g).rd = some (P g).c
  /-- The stored words are words. -/
  words : ∀ g < 128, ∀ j < 8, ldIdx g (P g) + 2 + j < m g → StoreOk (word (P g).vals j)
  ub : ∀ g < 128, u g = [] ∨ ∃ pc f, u g = [⟨pc, .ub f⟩] ∧
    ((m g = hd g + 1 ∧ rdCol (P g).rd = none) ∨
      (∃ j < 8, m g = ldIdx g (P g) + 2 + j ∧ ¬ StoreOk (word (P g).vals j)))
  out : ∀ g, 128 ≤ g → X.tr g = []

/-- Words of a load that is not yet made. -/
def vals0 : List Value := List.replicate 8 (b32 0)
/-- The bytes of a read that is not yet made. -/
def rd0 : List (Option Byte) := (b32 0).toBytes.map some

/-- A trace form: a prefix of the whole trace, possibly followed by undefined behaviour. -/
structure Form (A B D S g : Nat) (l : List Event) (P : Par) (m : Nat) (u : List Event) : Prop where
  tr : l = (fullE A B D S g P).take m ++ u
  len : m ≤ (fullE A B D S g P).length
  rd : P.rd.length = 4
  vals : P.vals.length = 8
  col : P.col < 2 ^ 16
  good : hd g + 1 < m → rdCol P.rd = some P.c
  words : ∀ j < 8, ldIdx g P + 2 + j < m → StoreOk (word P.vals j)
  ub : u = [] ∨ ∃ pc f, u = [⟨pc, .ub f⟩] ∧
    ((m = hd g + 1 ∧ rdCol P.rd = none) ∨
      (∃ j < 8, m = ldIdx g P + 2 + j ∧ ¬ StoreOk (word P.vals j)))

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}

theorem form_of_prefix {S g : Nat} {l : List Event} {P : Par} (hp : l <+: fullE A B D S g P)
    (hrd : P.rd.length = 4) (hv : P.vals.length = 8) (hc : P.col < 2 ^ 16)
    (hgood : hd g + 1 < l.length → rdCol P.rd = some P.c)
    (hw : ∀ j < 8, ldIdx g P + 2 + j < l.length → StoreOk (word P.vals j)) :
    Form A B D S g l P l.length [] :=
  ⟨by rw [List.append_nil]; exact List.prefix_iff_eq_take.mp hp, hp.length_le, hrd, hv, hc,
    hgood, hw, .inl rfl⟩

theorem vals0_length : vals0.length = 8 := rfl
theorem rd0_length : rd0.length = 4 := rfl

theorem words_vals0 : Words vals0 8 := by
  intro i hi; interval_cases i <;> exact storeOk_of_bytes rfl

/-! ### The prefixes of the whole trace -/

section
variable {S g col : Nat} {bs : List (Option Byte)} {c n0 n1 : Nat} {vals : List Value}

theorem fullE_eq (P : Par) : fullE A B D S g P = headE A B S g P.col ++ ([bar0E, rdE S P.rd] ++
    ((if g = 0 then midE S P.c P.n0 else []) ++ (List.replicate P.n1 (wait1E S false) ++
      lastE D S g P.c P.vals))) := by
  simp [fullE, preW1]

theorem pfx_head {k : Nat} : (headE A B S g col).take k <+: fullE A B D S g
    ⟨col, bs, c, n0, n1, vals⟩ :=
  (List.take_prefix _ _).trans (by rw [fullE_eq]; exact List.prefix_append _ _)

theorem pfx_bar : headE A B S g col ++ [bar0E] <+: fullE A B D S g ⟨col, bs, c, n0, n1, vals⟩ := by
  rw [fullE_eq]
  exact (List.prefix_append_right_inj _).mpr (List.prefix_append_of_prefix (by simp))

theorem pfx_rd : headE A B S g col ++ [bar0E] ++ [rdE S bs] <+:
    fullE A B D S g ⟨col, bs, c, n0, n1, vals⟩ := by
  rw [fullE_eq, List.append_assoc]
  exact (List.prefix_append_right_inj _).mpr (by simp)

theorem pfx_mid {n k : Nat} :
    headE A B S 0 col ++ [bar0E, rdE S bs] ++ List.replicate n (wait0E S false) ++
      [wait0E S true, mmaE S c].take k <+: fullE A B D S 0 ⟨col, bs, c, n, n1, vals⟩ := by
  rw [fullE_eq]
  simp only [↓reduceIte, midE, List.append_assoc]
  refine (List.prefix_append_right_inj _).mpr ((List.prefix_append_right_inj _).mpr
    ((List.prefix_append_right_inj _).mpr ?_))
  refine List.prefix_append_of_prefix ((List.take_prefix _ _).trans ?_)
  simp

theorem pfx_after {k : Nat} :
    preW1 A B S g col bs c n0 ++ List.replicate n1 (wait1E S false) ++
      (lastE D S g c vals).take k <+: fullE A B D S g ⟨col, bs, c, n0, n1, vals⟩ :=
  (List.prefix_append_right_inj _).mpr (List.take_prefix _ _)

theorem length_head {k : Nat} (hk : k ≤ (headE A B S g col).length) :
    ((headE A B S g col).take k).length = k := by simp; omega

theorem length_mid {n k : Nat} (hk : k ≤ 2) :
    (headE A B S 0 col ++ [bar0E, rdE S bs] ++ List.replicate n (wait0E S false) ++
      [wait0E S true, mmaE S c].take k).length = hd 0 + 1 + n + k := by
  have := headE_length (A := A) (B := B) (S := S) (g := 0) (col := col)
  simp; omega

theorem length_after {k : Nat} (hk : k ≤ 16) (_hk' : g / 32 = 0 ∨ k ≤ 15) :
    (preW1 A B S g col bs c n0 ++ List.replicate n1 (wait1E S false) ++
      (lastE D S g c vals).take k).length = tl g ⟨col, bs, c, n0, n1, vals⟩ + n1 + k := by
  have := headE_length (A := A) (B := B) (S := S) (g := g) (col := col)
  have hl : (lastE D S g c vals).length = if g / 32 = 0 then 17 else 16 := by
    unfold lastE; split_ifs <;> simp [storesE]
  simp only [preW1, tl, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, List.length_take, hl]
  split_ifs <;> simp [midE] <;> omega

end

/-! ### From the thread facts -/

section
variable (hpre : Pre L A B D a b mem0) (ht : ThreadFacts L A B D X)
  (hX : Consistent L kernel [] mem0 X)
include hpre ht hX

omit hpre ht hX in
/-- **The events before a state are a prefix of the whole trace.** -/
theorem along_form {g : Nat} {d : ThreadD} {pre : List Event} (hJ : Along L A B D g d pre) :
    ∃ P, Form A B D L.sharedBase g pre P pre.length [] := by
  obtain ⟨site, c, vals⟩ := d
  have hh := fun col => headE_length (A := A) (B := B) (S := L.sharedBase) (g := g) (col := col)
  -- the sites after the successful poll of `bar1`
  have after : ∀ {k : Nat} {vals' : List Value}, k ≤ 16 → (g / 32 = 0 ∨ k ≤ 15) →
      vals'.length = 8 → (lastE D L.sharedBase g c vals).take k =
        (lastE D L.sharedBase g c vals').take k → (∀ i < 8, i + 4 < k → StoreOk (word vals' i)) →
      After L A B D g ⟨site, c, vals⟩ k pre → ∃ P, Form A B D L.sharedBase g pre P pre.length [] :=
        by
    intro k vals' hk hk' hl htk hw hA
    obtain ⟨col, bs, n0, n, hc, hbs, hrd, rfl⟩ := hA
    have hlen := length_after (A := A) (B := B) (D := D) (S := L.sharedBase) (g := g) (col := col)
      (bs := bs) (c := c) (n0 := n0) (n1 := n) (vals := vals) hk hk'
    simp only [tl] at hlen
    refine ⟨⟨col, bs, c, n0, n, vals'⟩, form_of_prefix ?_ hbs hl hc (fun _ => hrd) ?_⟩
    · simp only at htk ⊢
      rw [htk]; exact pfx_after
    · intro j hj hlt
      rw [hlen] at hlt
      exact hw j hj (by simp only [ldIdx, tl] at hlt ⊢; omega)
  have mid : ∀ {k : Nat}, k ≤ 2 → Mid L A B g ⟨site, c, vals⟩ k pre →
      ∃ P, Form A B D L.sharedBase g pre P pre.length [] := by
    intro k hk hM
    obtain ⟨hg0, col, bs, n, hc, hbs, hrd, rfl⟩ := hM
    subst hg0
    exact ⟨⟨col, bs, c, n, 0, vals0⟩, form_of_prefix pfx_mid hbs rfl hc (fun _ => hrd)
      (by rw [length_mid hk]; simp [ldIdx, tl]; omega)⟩
  cases site <;> simp only [Along] at hJ
  · obtain ⟨-, rfl⟩ := hJ
    exact ⟨⟨0, rd0, 0, 0, 0, vals0⟩, form_of_prefix List.nil_prefix rfl rfl (by decide)
      (by simp) (by simp)⟩
  · obtain ⟨hg0, rfl⟩ := hJ
    subst hg0
    have h1 : [allocE L.sharedBase] = (headE A B L.sharedBase 0 0).take 1 := rfl
    exact ⟨⟨0, rd0, 0, 0, 0, vals0⟩, form_of_prefix (h1 ▸ pfx_head)
      rfl rfl (by decide) (by simp [hd]) (by simp [ldIdx, tl, hd])⟩
  all_goals try
    (obtain ⟨hg0, col, hc, rfl⟩ := hJ
     subst hg0
     have := hh col
     exact ⟨⟨col, rd0, 0, 0, 0, vals0⟩, form_of_prefix pfx_head rfl rfl hc
       (by simp [hd, headE]) (by simp [ldIdx, tl, hd, headE]; omega)⟩)
  · -- bar0
    obtain ⟨-, col, hc, rfl⟩ := hJ
    have := hh col
    refine ⟨⟨col, rd0, 0, 0, 0, vals0⟩, form_of_prefix ?_ rfl rfl hc (by omega)
      (by simp only [ldIdx, tl]; omega)⟩
    have := pfx_head (A := A) (B := B) (D := D) (S := L.sharedBase) (g := g) (col := col)
      (bs := rd0) (c := 0) (n0 := 0) (n1 := 0) (vals := vals0)
      (k := (headE A B L.sharedBase g col).length)
    rwa [List.take_length] at this
  · -- load
    obtain ⟨-, col, hc, rfl⟩ := hJ
    have := hh col
    exact ⟨⟨col, rd0, 0, 0, 0, vals0⟩, form_of_prefix pfx_bar rfl rfl hc (by simp; omega)
      (by simp only [ldIdx, tl, List.length_append, List.length_singleton]; omega)⟩
  · exact mid (by decide) hJ
  · exact mid (by decide) hJ
  · exact mid (by decide) hJ
  · exact after (k := 0) (vals' := vals0) (by decide) (.inr (by decide)) rfl (by simp)
      (by intro i _ h; omega) hJ
  · exact after (k := 1) (vals' := vals0) (by decide) (.inr (by decide)) rfl (by simp [lastE])
      (by intro i _ h; omega) hJ
  · exact after (k := 2) (vals' := vals0) (by decide) (.inr (by decide)) rfl (by simp [lastE])
      (by intro i _ h; omega) hJ
  · exact after (k := 3) (by decide) (.inr (by decide)) hJ.2 rfl (by intro i _ h; omega) hJ.1
  · obtain ⟨hA, hl, hj, hw⟩ := hJ
    exact after (k := 4 + _) (by omega) (.inr (by omega)) hl rfl
      (fun i _ h => hw i (by omega)) hA
  all_goals try
    exact after (by decide) (.inr (by decide)) hJ.2.1 rfl (fun i hi _ => hJ.2.2 i hi) hJ.1
  · obtain ⟨hw0, hA, hl, hw⟩ := hJ
    exact after (by decide) (.inl hw0) hl rfl (fun i hi _ => hw i hi) hA
  · obtain ⟨hA, hl, hw⟩ := hJ
    exact after (by split <;> decide) (by split <;> simp_all) hl rfl (fun i hi _ => hw i hi) hA

omit hpre ht hX in
/-- The machine's step at a state, from the state before and after an event. -/
theorem next_of_stop {g i : Nat} {d : ThreadD} {e : Event} (hei : X.get (g, i) = some e)
    (hs : stateAt L A B D X g i = some (some d)) (hs' : stateAt L A B D X g (i + 1) = none) :
    next g d e = none := by
  have h := Frame.stateAt_succ (C := code L A B D) (X := X) (g := g) (k := i) hei
  change Frame.stateAt (code L A B D) X g (i + 1) = none at hs'
  change Frame.stateAt (code L A B D) X g i = some (some d) at hs
  rw [h, hs] at hs'
  exact hs'

omit hpre in
/-- The event after a stop at a read whose bytes give no column is its thread's undefined
behaviour, and the last event. -/
theorem after_bad_read {g i : Nat} (hg : g < L.threads)
    (hs' : stateAt L A B D X g (i + 1) = none) (hlt : i + 1 < (X.tr g).length) :
    ∃ pc f, X.tr g = (X.tr g).take (i + 1) ++ [⟨pc, .ub f⟩] := by
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, i + 1) = some e1 := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨pc, f, bs, rfl, -⟩ := ht.dead hg he1 hs'
  have hend := end_last hX he1 (.inl ⟨f, rfl⟩)
  refine ⟨pc, f, ?_⟩
  conv_lhs => rw [← List.take_append_drop (i + 1) (X.tr g)]
  congr 1
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
  have : (X.tr g)[i + 1]? = some ⟨pc, .ub f⟩ := he1
  rw [List.getElem?_eq_getElem (by omega)] at this
  rw [Option.some.inj this]

omit hpre in
/-- **The trace of a launched thread** has a form. -/
theorem thread_form {g : Nat} (hg : g < L.threads) :
    ∃ P m u, Form A B D L.sharedBase g (X.tr g) P m u := by
  have hh := fun col => headE_length (A := A) (B := B) (S := L.sharedBase) (g := g) (col := col)
  cases hσ : stateAt L A B D X g (X.tr g).length with
  | some σ =>
    cases σ with
    | none => exact absurd hσ (ht.tracked g _ hg)
    | some d =>
      have hJ := ht.along hg le_rfl hσ
      rw [List.take_length] at hJ
      obtain ⟨P, hF⟩ := along_form hJ
      exact ⟨P, _, _, hF⟩
  | none =>
    obtain ⟨i, d, hi, hs, hs'⟩ := Frame.first_stop ht.tracked hg hσ
    obtain ⟨ei, hei⟩ : ∃ ei, X.get (g, i) = some ei := ⟨_, List.getElem?_eq_getElem hi⟩
    have hn := next_of_stop hei hs hs'
    have hev := ht.event hg hei hs
    have hJ := ht.along hg hi.le hs
    have htake : (X.tr g).take (i + 1) = (X.tr g).take i ++ [ei] := by
      rw [List.take_add_one]
      congr
      simpa [Execution.get] using hei
    have hilen : ((X.tr g).take i).length = i := by simp; omega
    obtain ⟨site, c, vals⟩ := d
    cases site <;> simp only [SiteEvent] at hev
    all_goals try first
      | (subst hev; simp [next] at hn; done)
      | (obtain ⟨_, _, rfl⟩ := hev; simp [next] at hn; done)
      | (obtain ⟨_, rfl⟩ := hev; simp [next, wait0E, wait1E] at hn; done)
      | (obtain ⟨_, _, rfl⟩ := hev; simp [next, ldE] at hn; done)
    · -- a read whose bytes give no column
      obtain ⟨bs, hbs, rfl⟩ := hev
      have hbad : rdCol bs = none := by
        simp only [next, rdE] at hn
        cases h : rdCol bs with
        | none => rfl
        | some c' => simp [h] at hn
      obtain ⟨-, col, hc, hpre'⟩ := hJ
      have hcol := hh col
      have hi' : i = hd g := by
        have := congrArg List.length hpre'
        simp only [hilen, List.length_append, List.length_singleton] at this
        omega
      have hp : (X.tr g).take (i + 1) <+: fullE A B D L.sharedBase g ⟨col, bs, 0, 0, 0, vals0⟩ := by
        rw [htake, hpre']
        exact pfx_rd
      have hlen1 : ((X.tr g).take (i + 1)).length = i + 1 := by simp; omega
      have hF : ∀ u, (u = [] ∨ ∃ pc f, u = [⟨pc, .ub f⟩]) →
          Form A B D L.sharedBase g ((X.tr g).take (i + 1) ++ u) ⟨col, bs, 0, 0, 0, vals0⟩ (i + 1) u
            := by
        intro u hu
        have hq := List.prefix_iff_eq_take.mp hp
        rw [hlen1] at hq
        refine ⟨by rw [← hq], by rw [← hlen1]; exact hp.length_le,
          hbs, rfl, hc, fun h => by omega, fun j _ h => by simp only [ldIdx, tl] at h; omega, ?_⟩
        rcases hu with rfl | ⟨pc, f, rfl⟩
        · exact .inl rfl
        · exact .inr ⟨pc, f, rfl, .inl ⟨by omega, hbad⟩⟩
      by_cases hl : i + 1 < (X.tr g).length
      · obtain ⟨pc, f, htr⟩ := after_bad_read ht hX hg hs' hl
        rw [htr]
        exact ⟨_, _, _, hF _ (.inr ⟨pc, f, rfl⟩)⟩
      · have htr : X.tr g = (X.tr g).take (i + 1) ++ [] := by
          rw [List.append_nil, List.take_of_length_le (by omega)]
        rw [htr]
        exact ⟨_, _, _, hF [] (.inl rfl)⟩
    · -- the undefined behaviour of a store
      rename_i j
      rcases hev with ⟨-, rfl⟩ | ⟨hb, f, rfl⟩
      · simp [next, stE] at hn
      have hend := end_last hX hei (.inl ⟨f, rfl⟩)
      obtain ⟨⟨col, bs, n0, n, hc, hbs, hrd, hpre'⟩, hl, hj, hw⟩ := hJ
      have hlen := length_after (A := A) (B := B) (D := D) (S := L.sharedBase) (g := g) (col := col)
        (bs := bs) (c := c) (n0 := n0) (n1 := n) (vals := vals) (k := 4 + j) (by omega)
          (.inr (by omega))
      rw [← hpre', hilen] at hlen
      have hp : (X.tr g).take i <+: fullE A B D L.sharedBase g ⟨col, bs, c, n0, n, vals⟩ := by
        rw [hpre']; exact pfx_after
      have htr : X.tr g = (X.tr g).take i ++ [⟨(Site.st j).pc, .ub f⟩] := by
        rw [← htake, List.take_of_length_le (by omega)]
      have hq := List.prefix_iff_eq_take.mp hp
      rw [hilen] at hq
      rw [htr]
      refine ⟨_, i, _, ⟨by rw [← hq], ?_, hbs, hl, hc, fun _ => hrd, ?_, ?_⟩⟩
      · rw [← hilen]; exact hp.length_le
      · intro j' hj' h
        exact hw j' (by simp only [ldIdx, tl] at h hlen ⊢; omega)
      · exact .inr ⟨_, f, rfl, .inr ⟨j, hj, by simp only [ldIdx, tl] at hlen ⊢; omega, hb⟩⟩
    · -- the exit
      subst hev
      have hend := end_last hX hei (.inr rfl)
      obtain ⟨⟨col, bs, n0, n, hc, hbs, hrd, hpre'⟩, hl, hw⟩ := hJ
      have hK : (lastE D L.sharedBase g c vals).take (if g / 32 = 0 then 16 else 15) ++ [exitE] =
          lastE D L.sharedBase g c vals := by
        have e : lastE D L.sharedBase g c vals = ([wait1E L.sharedBase true, fa1E, ldE g c vals,
            wldE] ++ storesE D g vals 8 ++ [fbE, bar1E, fa2E] ++
            (if g / 32 = 0 then [deallocE c] else [])) ++ [exitE] := rfl
        have hlen : (if g / 32 = 0 then 16 else 15) = ([wait1E L.sharedBase true, fa1E,
            ldE g c vals, wldE] ++ storesE D g vals 8 ++ [fbE, bar1E, fa2E] ++
            (if g / 32 = 0 then [deallocE c] else [])).length := by
          split_ifs <;> simp [storesE_length]
        rw [e, hlen, List.take_left]
      have htr : X.tr g = fullE A B D L.sharedBase g ⟨col, bs, c, n0, n, vals⟩ := by
        rw [← List.take_of_length_le (show (X.tr g).length ≤ i + 1 by omega), htake, hpre',
          List.append_assoc, hK]
        rfl
      refine
        ⟨⟨col, bs, c, n0, n, vals⟩, (fullE A B D L.sharedBase g ⟨col, bs, c, n0, n, vals⟩).length,
        [], ⟨by rw [htr, List.take_length, List.append_nil], le_rfl, hbs, hl, hc, fun _ => hrd,
          fun j hj _ => hw j hj, .inl rfl⟩⟩

/-- **Every execution has a description by its threads' whole traces.** -/
theorem wit : ∃ P m u, Wit A B D L.sharedBase X P m u := by
  have hT := threads_eq hpre
  have key : ∀ g, ∃ (P : Par) (m : Nat) (u : List Event),
      P.rd.length = 4 ∧ P.vals.length = 8 ∧ P.col < 2 ^ 16 ∧
        (g < 128 → Form A B D L.sharedBase g (X.tr g) P m u) := by
    intro g
    by_cases hg : g < 128
    · obtain ⟨P, m, u, h⟩ := thread_form ht hX (g := g) (by omega)
      exact ⟨P, m, u, h.rd, h.vals, h.col, fun _ => h⟩
    · exact ⟨⟨0, rd0, 0, 0, 0, vals0⟩, 0, [], rfl, rfl, by decide, fun h => absurd h hg⟩
  choose P m u hrd hv hc hP using key
  exact ⟨P, m, u, fun g hg => (hP g hg).tr, fun g hg => (hP g hg).len, hrd, hv, hc,
    fun g hg => (hP g hg).good, fun g hg => (hP g hg).words, fun g hg => (hP g hg).ub,
    fun g hg => hX.outside g (by omega)⟩

end

end

end PTX.Kernels.TcGemm.Proof
