-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.Region
public import Core.Assembly.Safety
public import Lemmas.Order.Order

@[expose] public section

/-! # Ordered regions exclude races

A proof tool for the conflict branches of `Unsafe`. The conflicting accesses of a set of bytes
are ordered (`ConflictsOrdered`) when, at every byte of the set that two conflicting accesses both
cover, one is visible to the other there. A kernel proves this region by region, each from the
protocol that guards it; once every byte is ordered, no race (`ConflictsOrdered.no_race`) and no
mixed-size conflict (`ConflictsOrdered.no_mixed`) remains. A region no conflict reaches is
ordered vacuously (`ConflictsOrdered.of_none`), and regions combine (`ConflictsOrdered.or`). -/

namespace PTX

variable {L : Launch} {X : Execution}

/-- Conflicting accesses of a byte satisfying `R` are ordered at that byte, one way or the
other. -/
def ConflictsOrdered (L : Launch) (X : Execution) (R : Loc → Prop) : Prop :=
  ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l →
    modelCausality L X l e f ∨ modelCausality L X l f e

/-- Two regions ordered are ordered together. -/
theorem ConflictsOrdered.or {R S : Loc → Prop} (hR : ConflictsOrdered L X R)
    (hS : ConflictsOrdered L X S) : ConflictsOrdered L X fun l => R l ∨ S l :=
  fun e f a b l hc ha hb hl => hl.elim (hR e f a b l hc ha hb) (hS e f a b l hc ha hb)

/-- An ordered region orders its subsets. -/
theorem ConflictsOrdered.mono {R S : Loc → Prop} (hR : ConflictsOrdered L X R)
    (h : ∀ l, S l → R l) : ConflictsOrdered L X S :=
  fun e f a b l hc ha hb hl => hR e f a b l hc ha hb (h l hl)

/-- A region no two conflicting accesses both cover is ordered. -/
theorem ConflictsOrdered.of_none {R : Loc → Prop}
    (h : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l → False) :
    ConflictsOrdered L X R :=
  fun e f a b l hc ha hb hl => (h e f a b l hc ha hb hl).elim

/-- **No race** once every byte's conflicts are ordered. -/
theorem ConflictsOrdered.no_race (h : ConflictsOrdered L X fun _ => True) : ¬ Race L X := by
  rintro ⟨e, f, a, b, l, hc, hs, ha, -, h1, h2, -⟩
  exact (h e f a b l hc ha ((hs.covers l).mp ha) trivial).elim
    (fun he => h1 (.direct he)) (fun hf => h2 (.direct hf))

/-- **Strong pairs ordered** once every byte's conflicts are ordered. -/
theorem ConflictsOrdered.strongOrdered (h : ConflictsOrdered L X fun _ => True) :
    StrongOrdered L X :=
  StrongOrdered.of_conflicts fun e f a b l hc ha hb => h e f a b l hc ha hb trivial

/-- **No mixed-size conflict** once every byte's conflicts are ordered. -/
theorem ConflictsOrdered.no_mixed (h : ConflictsOrdered L X fun _ => True) : ¬ Mixed L X := by
  rintro ⟨e, f, a, b, l, hc, -, ha, hb, h1, h2⟩
  exact (h e f a b l hc ha hb trivial).elim
    (fun he => h1 (.direct he)) (fun hf => h2 (.direct hf))

/-- **A read of a byte of an ordered region returns its latest visible write**: given a write of
the byte visible to the read, of which every other write of the byte visible to the read is
visible, the read's byte is that write's byte. As in `visible_write_reads`, the read is not the
read of an atomic read-modify-write. -/
theorem ConflictsOrdered.read_byte {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {R : Loc → Prop} (hX : Consistent L K A mem0 X) (hR : ConflictsOrdered L X R)
    {e w : AsyncCopy.Ref} {a dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (he : X.MemReads e a bs) {k : Nat} (hk : k < a.size)
    (hnr : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (e = .thread i ∧ X.Rmw i acc old new))
    (hl : R (a.loc.at k))
    (hw : X.MemWrites w dst written) (hc : dst.Covers (a.loc.at k))
    (hv : modelCausality L X (a.loc.at k) w e)
    (hlast : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
      modelCausality L X (a.loc.at k) w' e → w' = w ∨ modelCausality L X (a.loc.at k) w' w) :
    bs[k]? = some (wbyte dst written (a.loc.at k)) := by
  have hh := hX.hidden e a bs k w dst written he hk hw hc (.direct hv)
  have hrf := (hX.rf e a bs he).2 k hk
  cases hs : X.rf e k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hh hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    have hcon : Conflict X e source a dst' :=
      ⟨he.ne_write hsource hnr, false, true, he.intent, hsource.intent, .inr rfl,
        ⟨a.loc.at k, Acc.covers_at hk, hcov⟩⟩
    have hse : modelCausality L X (a.loc.at k) source e := by
      rcases hR e source a dst' _ hcon (Acc.covers_at hk) hcov hl with h | h
      · exact absurd (.direct h) (hX.noFuture e a bs k source he hk hs)
      · exact h
    rcases hlast source dst' bytes hsource hcov hse with hsame | hbefore
    · subst source
      obtain ⟨hfp, hbytes⟩ := hw.unique hsource
      rw [hbytes]
      simp only [wbyte, hfp.1]
      exact hvalue
    · exact False.elim (hh (.direct hbefore))


/-- **A read returns the bytes of its last visible write** of its footprint, once every byte's
conflicts are ordered: the write is visible at each byte, and every write of the byte visible to
the read is that write or visible to it. As in `visible_write_reads`, the read is not the read of
an atomic read-modify-write. -/
theorem ConflictsOrdered.read_of_last {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (h : ConflictsOrdered L X fun _ => True)
    {e w : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} {ws : List Byte}
    (he : X.MemReads e a bs)
    (hnr : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (e = .thread i ∧ X.Rmw i acc old new))
    (hw : X.MemWrites w a ws) (hlen : ws.length = a.size)
    (hv : ∀ k < a.size, modelCausality L X (a.loc.at k) w e)
    (hlast : ∀ k < a.size, ∀ w' a' ws', X.MemWrites w' a' ws' → a'.Covers (a.loc.at k) →
      modelCausality L X (a.loc.at k) w' e → w' = w ∨ modelCausality L X (a.loc.at k) w' w) :
    bs = ws.map some := by
  have hbl : bs.length = a.size := (hX.rf e a bs he).1
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.size
  · rw [h.read_byte hX he hk hnr trivial hw (Acc.covers_at hk) (hv k hk) (hlast k hk)]
    simp only [wbyte, Loc.at, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_eq_getElem (show k < ws.length by omega), Option.map_some]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

namespace Execution

/-- An MMA operand byte is in shared memory. -/
theorem mmaFootprint_shared {i : EvId} {isB : Bool} {idx : Nat} {l : Loc}
    (h : X.MmaFootprint i isB idx l) : l.space = .shared := by
  rcases h with ⟨d, s, acc, mask, -, hl⟩ | ⟨a, src, cta, -, -, hl⟩
  · unfold TcMma.OperandSpec.byteLoc at hl
    simp only [bind, Option.bind] at hl
    split_ifs at hl
    all_goals split at hl
    all_goals first
      | (cases hl; rfl)
      | cases hl
  · obtain ⟨-, -, hl⟩ := hl
    unfold TcCopy.byteLoc at hl
    split_ifs at hl
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hl
    rfl

/-- An MMA operand byte is in one of the operands' CTAs. -/
theorem _root_.PTX.TcMma.OperandSpec.byteLoc_cta {s : TcMma.OperandSpec} {op : TcMma.Operand}
    {idx : Nat} {l : Loc} (h : s.byteLoc op idx = some l) :
    l.cta = s.lowCta ∨ l.cta = s.highCta := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [bind, Option.bind] at h
  split_ifs at h
  all_goals split at h
  all_goals first
    | (cases h; first | exact .inl rfl | exact .inr rfl)
    | cases h

end Execution

end PTX
