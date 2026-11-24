-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Core.Assembly.Execution
public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.MBarrier.BarrierOrdinal
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Consequences of causality and byte-specific visibility

These are proofs from the Core rules. In particular, visible_write applies to ordinary
and independent asynchronous reads; it assumes neither a unique writer nor a copy-only
source. Memory order is per byte and is distinct from thread program order.

A read takes a visible latest write of each byte, up to writes of the same bytes with the same
value (`SameValueWrites`), when every conflicting pair at a byte some read covers, other than two
such writes, is ordered by visibility at that byte (`ReadsOrdered`, `visible_write_reads`). The
same-value pairs are the pairs ERR-DATA-RACE exempts because a read that may read from either
write reads the same bytes; they need no order. A safe execution has `ReadsOrdered` when the
strong pairs, which `Race` also exempts, are ordered (`StrongOrdered`, `ReadsOrdered.of_safe`). -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

theorem Acc.SameFootprint.covers {a b : Acc} (h : a.SameFootprint b) (l : Loc) :
    a.Covers l ↔ b.Covers l := by
  rcases h with ⟨hl,hs⟩
  simp only [Acc.Covers,hl,hs]

/-- Distinct elements of one vector access are on distinct bytes. -/
theorem SameAccess.not_overlap {e f : EvId} {a b : Acc} (h : SameAccess X e f) (hs : e.1 = f.1)
    (hlt : e.2 < f.2) (ha : (X.get e).bind Event.acc = some a)
    (hb : (X.get f).bind Event.acc = some b) : ¬ a.Overlap b := by
  have h2 := h.2 (f.2 - e.2) le_rfl
  have hf : (e.1, e.2 + (f.2 - e.2)) = f := Prod.ext hs (by simp only; omega)
  rw [hf, ha, hb] at h2
  obtain rfl : b = Acc.shift (f.2 - e.2) a := (Option.some.inj h2)
  rintro ⟨l, ⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩
  simp only [Acc.shift, Loc.at] at h5 h6 h7 h8
  have : a.size ≤ (f.2 - e.2) * a.size := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem Execution.Reads.access {e : EvId} {a : Acc} {bs : List (Option Byte)}
    (h : X.Reads e a bs) : X.Access e a false := .inl ⟨bs, h, rfl⟩

theorem Execution.Writes.access {e : EvId} {a : Acc} {bs : List Byte}
    (h : X.Writes e a bs) : X.Access e a true := .inr (.inl ⟨bs, h, rfl⟩)

theorem Execution.Reads.ne_write {e w : EvId} {a a' : Acc} {bs : List (Option Byte)}
    {bs' : List Byte} (h : X.Reads e a bs) (h' : X.Writes w a' bs') : e ≠ w := by
  rintro rfl
  obtain ⟨pc, hp⟩ := h; obtain ⟨pc', hp'⟩ := h'
  rw [hp] at hp'; cases hp'

theorem Execution.Writes.unique {e : EvId} {a a' : Acc} {bs bs' : List Byte}
    (h : X.Writes e a bs) (h' : X.Writes e a' bs') : a = a' ∧ bs = bs' := by
  obtain ⟨pc, hp⟩ := h; obtain ⟨pc', hp'⟩ := h'
  rw [hp] at hp'; cases hp'; exact ⟨rfl, rfl⟩

theorem Acc.covers_at {a : Acc} {k : Nat} (hk : k < a.size) : a.Covers (a.loc.at k) := by
  unfold Acc.Covers Loc.InRange Loc.at; simp; omega

theorem Execution.MemReads.intent {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)}
    (h : X.MemReads e a bs) : X.Intent e a false := by
  cases e with
  | thread e =>
    rcases h with hr | ⟨new, hr⟩
    · exact .inl ⟨bs, hr, rfl⟩
    · exact .inr (.inr ⟨bs, new, hr⟩)
  | async i p =>
    cases p <;> simp only [Execution.MemReads, Execution.Intent, AsyncCopy.Part.writes,
      Execution.AsyncFootprint] at h ⊢
    case readStore x y k =>
      obtain ⟨o, addr, b, _, hi, hl, _, hn, _⟩ := h
      exact ⟨True.intro, o.spec, addr, hi, hl, hn⟩
    case readCopy =>
      obtain ⟨dst, m, hi, hs, _⟩ := h
      exact ⟨True.intro, .inl ⟨dst, hi, hs⟩⟩
    case mmaRead b k =>
      obtain ⟨b, hi, hn, _⟩ := h
      exact ⟨True.intro, hn, hi.1⟩
    case readLoad x y k =>
      obtain ⟨o, addr, b, _, hi, hl, _, hn, _⟩ := h
      exact ⟨True.intro, o.spec, addr, hi, hl, hn⟩
    case oldStore x y k =>
      obtain ⟨o, addr, b, _, hi, hred, hl, _, hn, _⟩ := h
      exact ⟨True.intro, o.spec, addr, hi, hred, hl, hn⟩
    case oldElem j =>
      obtain ⟨s, r, raw, hi, hred, hel, _, _⟩ := h
      exact ⟨True.intro, s, r, hi, hred, hel⟩

theorem Execution.MemWrites.intent {e : AsyncCopy.Ref} {a : Acc} {bs : List Byte}
    (h : X.MemWrites e a bs) : X.Intent e a true := by
  cases e with
  | thread e =>
    rcases h with hw | ⟨old, hw⟩
    · exact .inr (.inl ⟨bs, hw, rfl⟩)
    · exact .inr (.inr ⟨old, some bs, hw⟩)
  | async i p =>
    cases p <;> simp only [Execution.MemWrites, Execution.Intent, AsyncCopy.Part.writes,
      Execution.AsyncFootprint] at h ⊢
    case writeLoad x y k =>
      obtain ⟨o, addr, b, _, hi, hl, _, hn, _⟩ := h
      exact ⟨True.intro, o.spec, addr, hi, hl, hn⟩
    case writeCta c =>
      obtain ⟨s, ts, hi, ht, _, r, _, ha, _⟩ := h
      exact ⟨True.intro, s, ts, hi, ht, ha⟩
    case writeCopy =>
      obtain ⟨src, hi, hw, hd, _⟩ := h
      exact ⟨True.intro, src, hi, hw, hd⟩
    case writeElem j =>
      obtain ⟨src, hi, hel, _⟩ := h
      exact ⟨True.intro, src, hi, hel⟩
    case writeStore x y k =>
      obtain ⟨o, addr, b, _, hi, hl, _, hn, _⟩ := h
      exact ⟨True.intro, o.spec, addr, hi, hl, hn⟩

/-- Only an atomic read-modify-write reads and writes at one reference. A read that is not the
read of one never coincides with a write. -/
theorem Execution.MemReads.ne_write {e w : AsyncCopy.Ref} {a a' : Acc}
    {bs : List (Option Byte)} {bs' : List Byte}
    (hr : X.MemReads e a bs) (hw : X.MemWrites w a' bs')
    (hn : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (e = .thread i ∧ X.Rmw i acc old new)) : e ≠ w := by
  rintro rfl
  cases e with
  | thread i =>
    have hnr : ∀ pc acc old new, X.get i ≠ some ⟨pc, .rmw acc old new⟩ :=
      fun pc acc old new hget => hn i acc old new ⟨rfl, ⟨pc, hget⟩⟩
    rw [Execution.memReads_thread_iff_of_not_rmw hnr] at hr
    rw [Execution.memWrites_thread_iff_of_not_rmw hnr] at hw
    obtain ⟨pc, hp⟩ := hr
    obtain ⟨pc', hp'⟩ := hw
    rw [hp] at hp'
    cases hp'
  | async i p => cases p <;> simp_all [Execution.MemReads, Execution.MemWrites]

/-- The two writes of one reference have the same footprint and the same bytes: only the memory
qualifiers of a tensor stage's footprint are unconstrained. -/
theorem Execution.MemWrites.unique {e : AsyncCopy.Ref} {a a' : Acc} {bs bs' : List Byte}
    (h : X.MemWrites e a bs) (h' : X.MemWrites e a' bs') :
    a.SameFootprint a' ∧ bs = bs' := by
  cases e with
  | thread e =>
    rcases h with hw | ⟨old, hr⟩
    · rcases h' with hw' | ⟨old', hr'⟩
      · obtain ⟨rfl, rfl⟩ := Execution.Writes.unique hw hw'
        exact ⟨⟨rfl, rfl⟩, rfl⟩
      · obtain ⟨pc, hp⟩ := hw
        obtain ⟨pc', hp'⟩ := hr'
        rw [hp] at hp'
        cases hp'
    · rcases h' with hw' | ⟨old', hr'⟩
      · obtain ⟨pc, hp⟩ := hr
        obtain ⟨pc', hp'⟩ := hw'
        rw [hp] at hp'
        cases hp'
      · obtain ⟨pc, hp⟩ := hr
        obtain ⟨pc', hp'⟩ := hr'
        rw [hp] at hp'
        cases hp'
        exact ⟨⟨rfl, rfl⟩, rfl⟩
  | async i p =>
    cases p <;> simp only [Execution.MemWrites] at h h'
    case writeLoad x y k =>
      obtain ⟨o, addr, b, ho, _, hl, hb, hn, hbs, hqa, hqr, hqs⟩ := h
      obtain ⟨o', addr', b', ho', _, hl', hb', hn', hbs', hqa', hqr', hqs'⟩ := h'
      rw [ho] at ho'; cases ho'
      have hloc : a.loc = a'.loc := Option.some.inj (hl.symm.trans hl')
      have hbyte : b = b' := Option.some.inj (hb.symm.trans hb')
      exact ⟨⟨hloc, by rw [hn, hn']⟩, by rw [hbs, hbs', hbyte]⟩
    case writeStore x y k =>
      obtain ⟨o, addr, b, ho, _, hl, hb, hn, hbs, hqa, hqr, hqs⟩ := h
      obtain ⟨o', addr', b', ho', _, hl', hb', hn', hbs', hqa', hqr', hqs'⟩ := h'
      rw [ho] at ho'; cases ho'
      have hloc : a.loc = a'.loc := Option.some.inj (hl.symm.trans hl')
      have hbyte : b = b' := Option.some.inj (hb.symm.trans hb')
      exact ⟨⟨hloc, by rw [hn, hn']⟩, by rw [hbs, hbs', hbyte]⟩
    case writeCta c =>
      obtain ⟨s, ts, ⟨pc, hi⟩, _, _, r, hr, ha, hb⟩ := h
      obtain ⟨s', ts', ⟨pc', hi'⟩, _, _, r', hr', ha', hb'⟩ := h'
      rw [hi] at hi'; cases hi'
      rw [hr] at hr'; cases hr'
      exact ⟨⟨by rw [ha, ha'], by rw [ha, ha']⟩, hb.trans hb'.symm⟩
    case writeCopy =>
      obtain ⟨src, ⟨pc, hi⟩, -, hd, hb⟩ := h
      obtain ⟨src', ⟨pc', hi'⟩, -, hd', hb'⟩ := h'
      rw [hi] at hi'
      cases hi'
      rw [hb] at hb'
      cases hb'
      exact ⟨⟨by rw [← hd, ← hd'], by rw [← hd, ← hd']⟩, rfl⟩
    case writeElem j =>
      obtain ⟨src, ⟨pc, hi⟩, hel, hb⟩ := h
      obtain ⟨src', ⟨pc', hi'⟩, hel', hb'⟩ := h'
      rw [hi] at hi'
      cases hi'
      rw [hel] at hel'
      cases hel'
      rw [hb] at hb'
      cases hb'
      exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The strong pairs (§8.7.1), which `Race` exempts other than by visibility, are ordered by
visibility at their common bytes. -/
def StrongOrdered (L : Launch) (X : Execution) : Prop :=
  ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l →
    StrongScoped L X e a f.issuer.1 ∧ StrongScoped L X f b e.issuer.1 →
    modelCausality L X l e f ∨ modelCausality L X l f e

/-- Every conflicting pair ordered by visibility: in particular the strong ones. -/
theorem StrongOrdered.of_conflicts
    (h : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l →
      modelCausality L X l e f ∨ modelCausality L X l f e) : StrongOrdered L X :=
  fun e f a b l hc ha hb _ => h e f a b l hc ha hb

theorem Execution.Access.lt {e : EvId} {a : Acc} {w : Bool} (h : X.Access e a w) :
    e.2 < (X.tr e.1).length := by
  rcases h with ⟨bs, ⟨pc, hp⟩, -⟩ | ⟨bs, ⟨pc, hp⟩, -⟩ | ⟨old, new, ⟨pc, hp⟩⟩ <;> exact len_of_get hp

theorem Execution.Access.acc {e : EvId} {a : Acc} {w : Bool} (h : X.Access e a w) :
    (X.get e).bind Event.acc = some a := by
  rcases h with ⟨bs, ⟨pc, hp⟩, -⟩ | ⟨bs, ⟨pc, hp⟩, -⟩ | ⟨old, new, ⟨pc, hp⟩⟩ <;>
    simp [hp, Event.acc]

theorem Acc.Overlap.symm {a b : Acc} (h : a.Overlap b) : b.Overlap a :=
  let ⟨l, h1, h2⟩ := h; ⟨l, h2, h1⟩

/-- Overlapping accesses of one thread are in program order. -/
theorem po_of_overlap {e f : EvId} {a b : Acc} {we wf : Bool} (he : X.Access e a we)
    (hf : X.Access f b wf) (hs : e.1 = f.1) (hlt : e.2 < f.2) (hov : a.Overlap b) : po X e f :=
  ⟨hs, hlt, hf.lt, fun h => h.not_overlap hs hlt he.acc hf.acc hov⟩

/-- All overlapping bytes of safe conflicting accesses that are not two writes of the same
value have an order. -/
theorem ordered_of_safe (hm : ¬ Mixed L X) (hr : ¬ Race L X) (hs : StrongOrdered L X)
    {e f : AsyncCopy.Ref} {a b : Acc} {l : Loc}
    (hc : Conflict X e f a b) (hsv : ¬ SameValueWrites X e f a b) (ha : a.Covers l)
    (hb : b.Covers l) :
    ByteCausality L X l e f ∨ ByteCausality L X l f e := by
  by_cases hab : a.SameFootprint b
  · by_cases hms : MorallyStrong L X e f a b
    · rcases hms with ⟨⟨i, j, rfl, rfl, hij⟩ | ⟨h1, h2⟩, -, -⟩
      · obtain ⟨hne, we, wf, hi, hj, -, hov⟩ := hc
        have hne' : i.2 ≠ j.2 := fun h => hne (by rw [Prod.ext hij h])
        rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
        · exact .inl (.direct (.inl (.single (.inl (po_of_overlap hi hj hij hlt hov)))))
        · exact .inr (.direct (.inl (.single (.inl (po_of_overlap hj hi hij.symm hlt hov.symm)))))
      · exact (hs e f a b l hc ha hb ⟨h1, h2⟩).imp .direct .direct
    · by_contra hno
      push Not at hno
      exact hr ⟨e, f, a, b, l, hc, hab, ha, hms, hno.1, hno.2, hsv⟩
  · by_contra hno
    push Not at hno
    exact hm ⟨e, f, a, b, l, hc, hab, ha, hb, hno.1, hno.2⟩

/-- Every conflicting pair at a byte that a read covers, other than two writes of the same bytes
with the same value (`SameValueWrites`), is ordered by visibility at that byte. -/
def ReadsOrdered (L : Launch) (X : Execution) : Prop :=
  ∀ (r : AsyncCopy.Ref) (ra : Acc) (rbs : List (Option Byte)) (k : Nat), X.MemReads r ra rbs →
    k < ra.size → ∀ e f a b, Conflict X e f a b → ¬ SameValueWrites X e f a b →
      a.Covers (ra.loc.at k) → b.Covers (ra.loc.at k) →
        ByteCausality L X (ra.loc.at k) e f ∨ ByteCausality L X (ra.loc.at k) f e

/-- A safe execution orders its conflicts at the bytes that are read, but for the same-value
write pairs, once its strong pairs are ordered. -/
theorem ReadsOrdered.of_safe (hm : ¬ Mixed L X) (hr : ¬ Race L X) (hs : StrongOrdered L X) :
    ReadsOrdered L X :=
  fun _ _ _ _ _ _ _ _ _ _ hc hsv ha hb => ordered_of_safe hm hr hs hc hsv ha hb

/-- A read that is not the read of an atomic read-modify-write has no write intent at its own
footprint, so it is in no same-value write pair. -/
theorem Execution.MemReads.not_write {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)}
    (he : X.MemReads e a bs)
    (hnr : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (e = .thread i ∧ X.Rmw i acc old new)) : ¬ X.Intent e a true := by
  intro hi
  cases e with
  | thread i =>
    rcases he with ⟨pc, hp⟩ | ⟨new, hr⟩
    · rcases hi with ⟨_, -, h⟩ | ⟨_, ⟨pc', hp'⟩, -⟩ | ⟨old, new, hr⟩
      · cases h
      · rw [hp] at hp'; cases hp'
      · exact hnr i a old new ⟨rfl, hr⟩
    · exact hnr i a bs new ⟨rfl, hr⟩
  | async i p =>
    have h0 := he.intent
    simp only [Execution.Intent] at h0 hi
    exact Bool.noConfusion (h0.1.trans hi.1.symm)

/-- **A read takes a visible latest write of each byte**, or W0 when no write is visible, when
the conflicts at the bytes that are read are ordered: every other write of the byte visible to the
read is visible to the source or writes the source's bytes with the source's value. The proof
treats ordinary, copy and MMA reads uniformly. The read is not the read of an atomic
read-modify-write (`hnr`): such a read may read a byte from its own write, and no causality order
relates an event to itself. -/
theorem visible_write_reads {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X)
    {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} (he : X.MemReads e a bs) {k : Nat}
    (hk : k < a.size)
    (hnr : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (e = .thread i ∧ X.Rmw i acc old new)) :
    match X.rf e k with
    | none => ∀ w a' bs', X.MemWrites w a' bs' → a'.Covers (a.loc.at k) →
        ¬ ByteCausality L X (a.loc.at k) w e
    | some w => ByteCausality L X (a.loc.at k) w e ∧
        ∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers (a.loc.at k) →
          ByteCausality L X (a.loc.at k) w' e → w' = w ∨ ByteCausality L X (a.loc.at k) w' w ∨
            ∃ a0 bs0, X.MemWrites w a0 bs0 ∧ SameValueWrites X w' w a' a0 := by
  have hrf := (hX.rf e a bs he).2 k hk
  cases hsrc : X.rf e k with
  | none =>
    intro w a' bs' hw hcov hwe
    have hh := hX.hidden e a bs k w a' bs' he hk hw hcov hwe
    rw [hsrc] at hh
    exact hh
  | some w =>
    rw [hsrc] at hrf
    obtain ⟨a', bs', hw, hcov, _⟩ := hrf
    have hc : Conflict X e w a a' :=
      ⟨he.ne_write hw hnr, false, true, he.intent, hw.intent, .inr rfl,
        ⟨a.loc.at k, Acc.covers_at hk, hcov⟩⟩
    have hnsv : ¬ SameValueWrites X e w a a' := fun h => he.not_write hnr h.1
    have hwe : ByteCausality L X (a.loc.at k) w e := by
      rcases hord e a bs k he hk e w a a' hc hnsv (Acc.covers_at hk) hcov with h | h
      · exact absurd h (hX.noFuture e a bs k w he hk hsrc)
      · exact h
    refine ⟨hwe, fun w' a'' bs'' hw' hcov' hw'e => ?_⟩
    by_cases hne : w' = w
    · exact .inl hne
    · right
      by_cases hsv : SameValueWrites X w' w a'' a'
      · exact .inr ⟨a', bs', hw, hsv⟩
      left
      have hh := hX.hidden e a bs k w' a'' bs'' he hk hw' hcov' hw'e
      rw [hsrc] at hh
      have hc' : Conflict X w' w a'' a' :=
        ⟨hne, true, true, hw'.intent, hw.intent, .inl rfl, ⟨a.loc.at k, hcov', hcov⟩⟩
      exact (hord e a bs k he hk w' w a'' a' hc' hsv hcov' hcov).resolve_right hh

/-- Every safe read chooses a visible latest write to each byte, or W0 when no write
is visible. As in `visible_write_reads`, the read is not the read of an atomic read-modify-write
(`hnr`). -/
theorem visible_write {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X) (hr : ¬ Race L X) (hs : StrongOrdered L X)
    {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} (he : X.MemReads e a bs) {k : Nat}
    (hk : k < a.size)
    (hnr : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (e = .thread i ∧ X.Rmw i acc old new)) :
    match X.rf e k with
    | none => ∀ w a' bs', X.MemWrites w a' bs' → a'.Covers (a.loc.at k) →
        ¬ ByteCausality L X (a.loc.at k) w e
    | some w => ByteCausality L X (a.loc.at k) w e ∧
        ∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers (a.loc.at k) →
          ByteCausality L X (a.loc.at k) w' e → w' = w ∨ ByteCausality L X (a.loc.at k) w' w ∨
            ∃ a0 bs0, X.MemWrites w a0 bs0 ∧ SameValueWrites X w' w a' a0 :=
  visible_write_reads hX (.of_safe hm hr hs) he hk hnr

/-- A program proof identifies the latest visible writer of this byte. Other writers
are allowed before it, after the read, or unordered with it when they write its bytes with its
value; no global sole-writer hypothesis is needed. As in `visible_write_reads`, the read is not the
read of an atomic read-modify-write (`hnr`). -/
theorem read_byte_of_latest {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X) (hr : ¬ Race L X) (hs : StrongOrdered L X)
    {e w : AsyncCopy.Ref} {a dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (he : X.MemReads e a bs) {k : Nat} (hk : k < a.size)
    (hnr : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (e = .thread i ∧ X.Rmw i acc old new))
    (hw : X.MemWrites w dst written) (hc : dst.Covers (a.loc.at k))
    (hv : modelCausality L X (a.loc.at k) w e)
    (hlast : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
      ByteCausality L X (a.loc.at k) w' e → w' = w ∨ ByteCausality L X (a.loc.at k) w' w ∨
        SameValueWrites X w' w dst' dst) :
    bs[k]? = some (wbyte dst written (a.loc.at k)) := by
  have hh := hX.hidden e a bs k w dst written he hk hw hc (.direct hv)
  have hlatest := visible_write hX hm hr hs he hk hnr
  have hrf := (hX.rf e a bs he).2 k hk
  cases hs : X.rf e k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hh hlatest hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    rcases hlast source dst' bytes hsource hcov hlatest.1 with hsame | hbefore | hsv
    · subst source
      obtain ⟨hfp, hbytes⟩ := hw.unique hsource
      rw [hbytes]
      simp only [wbyte, hfp.1]
      exact hvalue
    · exact False.elim (hh hbefore)
    · obtain ⟨-, -, hfp, hval⟩ := hsv
      rw [← hval bytes written hsource hw]
      simp only [wbyte, ← hfp.1]
      exact hvalue

theorem vis_chain_irrefl (hac : ∀ n, ¬ Relation.TransGen (stageCausality L X) n n) {e : EvId} :
    ¬ Relation.TransGen (baseCausality L X) e e := by
  intro h
  have collapse {a b : EvId}
      (h : Relation.TransGen (baseCausality L X) a b) : baseCausality L X a b := by
    induction h with
    | single h => exact h
    | tail _ h ih => exact ih.trans h
  exact baseCausality_irrefl hac (collapse h)

/-- `CompletionBefore` into `f` is determined by causality and the proxy fences into `f`. -/
theorem completionBefore_old {Y : Execution} {l : Loc} {f : EvId}
    (hh : ∀ {w}, _root_.PTX.baseCausality L Y w f ↔ _root_.PTX.baseCausality L X w f)
    (hp : ∀ {w}, ProxyBefore L Y w f l ↔ ProxyBefore L X w f l) {p : AsyncCopy.Part} {w : EvId} :
    CompletionBefore L Y l p w f ↔ CompletionBefore L X l p w f := by
  cases p <;> simp only [CompletionBefore, hh, hp]

/-- `CompletionBefore` is determined by causality and the proxy fences. -/
theorem completionBefore_congr {Y : Execution} {l : Loc}
    (hh : ∀ e f, _root_.PTX.baseCausality L Y e f ↔ _root_.PTX.baseCausality L X e f)
    (hp : ∀ e f, ProxyBefore L Y e f l ↔ ProxyBefore L X e f l) (p : AsyncCopy.Part) (w f : EvId) :
    CompletionBefore L Y l p w f ↔ CompletionBefore L X l p w f := by
  cases p <;> simp only [CompletionBefore, hh, hp]

/-- Transport a completion path, including copy-source reuse, through a frame. -/
theorem observedCompletionBefore_congr {Y : Execution} {l : Loc} {i w f : EvId}
    {p : AsyncCopy.Part} (hi : Y.get i = X.get i) (hf : Y.get f = X.get f)
    (hh : _root_.PTX.baseCausality L Y w f ↔ _root_.PTX.baseCausality L X w f)
    (hp : ProxyBefore L Y w f l ↔ ProxyBefore L X w f l) :
    ObservedCompletionBefore L Y l i p w f ↔ ObservedCompletionBefore L X l i p w f :=
  or_congr (by cases p <;> first | exact hh | exact hp)
    (TcReadReuseBefore.congr L hi hf hh)

/-- Reflect an observed completion into an execution containing its witnesses. -/
theorem observedCompletionBefore_map {Y : Execution} {l : Loc} {i w f : EvId}
    {p : AsyncCopy.Part} (hc : ∀ {s}, Y.CpIssue i s → X.CpIssue i s)
    (hm : ∀ {d s accum mask}, Y.MmaIssue i d s accum mask → X.MmaIssue i d s accum mask)
    (hw : ∀ {a bs}, Y.Writes f a bs → X.Writes f a bs)
    (hh : _root_.PTX.baseCausality L Y w f → _root_.PTX.baseCausality L X w f)
    (hp : ProxyBefore L Y w f l → ProxyBefore L X w f l) :
    ObservedCompletionBefore L Y l i p w f → ObservedCompletionBefore L X l i p w f := by
  rintro (h | h)
  · exact Or.inl (by cases p <;> first | exact hh h | exact hp h)
  · apply Or.inr
    cases p <;> try exact h
    case mmaRead isB index =>
      obtain ⟨hs, hIssue, hb, a, bs, hwr, hcov⟩ := h
      refine ⟨hs, ?_, hh hb, a, bs, hw hwr, hcov⟩
      rcases hIssue with ⟨hB, s, hcp⟩ | ⟨hSame, hLt, d, s, accum, mask, hmma⟩
      · exact .inl ⟨hB, s, hc hcp⟩
      · exact .inr ⟨hSame, hLt, d, s, accum, mask, hm hmma⟩

end

end

end PTX
