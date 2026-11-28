-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Kinds

@[expose] public section

/-! # The data machine along the trace

`InvD l d`: a followed data state `d` after the events `l` of its lane holds what the trace's
last loads read: the partial scale vector (the last `el` scale-load elements), the row's scale
word (the last four elements of the row's scale load) and each raw word done in the row (the
last load at its pc). It is kept by every followed step (`invD_step`). On valid data
(`GoodEv`) the data machine follows wherever the control machine follows (`dataNext_ok`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-! ### Trace words and the data machine's words -/

def readVal (e : Event) : Value :=
  match e.kind with
  | .rd _ bs => loadVal bs
  | _ => .pred false

theorem readWord_eq (n : Nat) (e : Event) : readWord n e = wordOf n (readVal e) := by
  obtain ⟨pc, k⟩ := e
  cases k with
  | rd a bs =>
    simp only [readWord, readVal, loadVal]
    cases (rebuild 3 bs).toOption with
    | none => rfl
    | some v => cases v <;> rfl
  | _ => rfl

theorem bitsWord_lt {n x : Nat} {v : Value} (h : wordOf n v = some x) : x < 2 ^ n := by
  unfold wordOf at h
  split at h
  · split at h
    · cases h; omega
    · cases h
  · cases h

def atPc (l : List Event) (p : Nat) : List Event := l.filter fun e => decide (e.pc = p)

theorem atPc_snoc (l : List Event) (e : Event) (p : Nat) :
    atPc (l ++ [e]) p = atPc l p ++ (if e.pc = p then [e] else []) := by
  unfold atPc
  rw [List.filter_append]
  by_cases h : e.pc = p <;> simp [h]

theorem atPc_ne {l : List Event} {e : Event} {p : Nat} (h : e.pc ≠ p) :
    atPc (l ++ [e]) p = atPc l p := by
  rw [atPc_snoc]; simp [h]

theorem atPc_eq {l : List Event} {e : Event} {p : Nat} (h : e.pc = p) :
    atPc (l ++ [e]) p = atPc l p ++ [e] := by
  rw [atPc_snoc]; simp [h]

theorem lastN_snoc {α : Type} (n : Nat) (l : List α) (x : α) :
    lastN (n + 1) (l ++ [x]) = lastN n l ++ [x] := by
  unfold lastN
  rw [List.length_append, List.length_singleton, Nat.add_sub_add_right,
    List.drop_append_of_le_length (by omega)]

theorem lastN_length {α : Type} {n : Nat} {l : List α} (h : n ≤ l.length) :
    (lastN n l).length = n := by
  unfold lastN; rw [List.length_drop]; omega

/-! ### The invariant -/

def InRow : Site → Fin 4 → Bool
  | .raw r' _, r => r' = r
  | .store r' _, r => r' = r
  | _, _ => false

def Done : Site → Fin 4 → Fin 8 → Bool
  | .raw r' s', r, i => r' = r ∧ i.val < s'.val
  | .store r' s', r, i => r' = r ∧ i.val ≤ s'.val + 1
  | _, _, _ => false

/-- An event of a row of a block: a scale load, a raw load or a chunk store. -/
def RowPc (e : Event) : Prop := 2695 ≤ e.pc ∧ e.pc ≤ 3594

/-- The last `n` events at pc `p` all come after a point from which every event is a row event
(no poll, no arrival among them). -/
def Since (l : List Event) (p n : Nat) : Prop :=
  ∃ l1 l2, l = l1 ++ l2 ∧ n ≤ (atPc l2 p).length ∧ ∀ x ∈ l2, RowPc x

theorem ite0_ne {p : Prop} [Decidable p] {a : Nat} (h : ¬p) : (if p then a else 0) = 0 := by
  simp [h]

theorem ite0_eq {p : Prop} [Decidable p] {a : Nat} (h : p) : (if p then a else 0) = a := by
  simp [h]

theorem since_zero (l : List Event) (p : Nat) : Since l p 0 :=
  ⟨l, [], by simp, Nat.zero_le _, by simp⟩

theorem since_snoc_ne {l : List Event} {e : Event} {p n : Nat} (h : Since l p n) (he : RowPc e)
    (hne : e.pc ≠ p) : Since (l ++ [e]) p n := by
  obtain ⟨l1, l2, rfl, hn, hr⟩ := h
  refine ⟨l1, l2 ++ [e], by simp, ?_, ?_⟩
  · rw [atPc_ne hne]; exact hn
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hr x hx
    · obtain rfl := List.mem_singleton.mp hx; exact he

theorem since_snoc_eq {l : List Event} {e : Event} {p n : Nat} (h : Since l p n) (he : RowPc e)
    (heq : e.pc = p) : Since (l ++ [e]) p (n + 1) := by
  obtain ⟨l1, l2, rfl, hn, hr⟩ := h
  refine ⟨l1, l2 ++ [e], by simp, ?_, ?_⟩
  · rw [atPc_eq heq, List.length_append, List.length_singleton]; omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hr x hx
    · obtain rfl := List.mem_singleton.mp hx; exact he

theorem since_one {l : List Event} {e : Event} {p : Nat} (he : RowPc e) (heq : e.pc = p) :
    Since (l ++ [e]) p 1 :=
  ⟨l, [e], rfl, by simp [atPc, heq], by simp [he]⟩

/-- **The invariant**: the partial scale vector, the row's scale word and the raw words are what
the trace's last loads read. -/
structure InvD (l : List Event) (d : D) : Prop where
  acc : ∀ r : Fin 4, d.c.site = .scale r → d.c.el ≤ (atPc l (dqScalePc r)).length ∧
    d.c.acc = (lastN d.c.el (atPc l (dqScalePc r))).map readVal
  sc : ∀ r, InRow d.c.site r → d.sc = scaleWordOf (lastN 4 (atPc l (dqScalePc r)))
  ws : ∀ r i, Done d.c.site r i → d.ws i = rawWordOf (lastN 1 (atPc l (dqRawPc r i)))
  pos : ∀ r : Fin 4, (atPc l (dqScalePc r)).length % 4 =
    if d.c.site = .scale r then d.c.el else 0
  qsw : ∀ r : Fin 4, d.c.site = .scale r → Since l (dqScalePc r) d.c.el
  qsc : ∀ r, InRow d.c.site r → Since l (dqScalePc r) 4
  qrw : ∀ r i, Done d.c.site r i → Since l (dqRawPc r i) 1

theorem scale_pc (r : Fin 4) : (Site.scale r).pc = dqScalePc r := by
  simp only [Site.pc, rowBase, dqScalePc]; omega

theorem raw_pc (r : Fin 4) (s : Fin 8) : (Site.raw r s).pc = dqRawPc r s := by
  simp only [Site.pc, rowBase, dqRawPc]; split_ifs <;> omega

theorem store_pc (r : Fin 4) (s : Fin 8) : (Site.store r s).pc = dqStorePc r s := by
  simp only [Site.pc, rowBase, dqStorePc]; split_ifs <;> omega

theorem raw_inj {r r' : Fin 4} {s i : Fin 8} (h : (Site.raw r s).pc = dqRawPc r' i) :
    r = r' ∧ s = i := by
  have := r.isLt; have := r'.isLt; have := s.isLt; have := i.isLt
  rw [raw_pc] at h
  unfold dqRawPc at h
  constructor <;> apply Fin.ext <;> split_ifs at h <;> omega

theorem raw_ne_scale (r r' : Fin 4) (s : Fin 8) : (Site.raw r s).pc ≠ dqScalePc r' := by
  have := r.isLt; have := r'.isLt; have := s.isLt
  rw [raw_pc]; unfold dqRawPc dqScalePc; split_ifs <;> omega

theorem store_ne_raw (r r' : Fin 4) (s i : Fin 8) : (Site.store r s).pc ≠ dqRawPc r' i := by
  have := r.isLt; have := r'.isLt; have := s.isLt; have := i.isLt
  rw [store_pc]; unfold dqRawPc dqStorePc; split_ifs <;> omega

theorem store_ne_scale (r r' : Fin 4) (s : Fin 8) : (Site.store r s).pc ≠ dqScalePc r' := by
  have := r.isLt; have := r'.isLt; have := s.isLt
  rw [store_pc]; unfold dqStorePc dqScalePc; split_ifs <;> omega

theorem scale_ne_raw (r r' : Fin 4) (i : Fin 8) : (Site.scale r).pc ≠ dqRawPc r' i := by
  have := r.isLt; have := r'.isLt; have := i.isLt
  rw [scale_pc]; unfold dqRawPc dqScalePc; split_ifs <;> omega

theorem scalePc_inj {r r' : Fin 4} (h : dqScalePc r = dqScalePc r') : r = r' := by
  have := r.isLt; have := r'.isLt
  unfold dqScalePc at h
  exact Fin.ext (by omega)

theorem scale_rowPc (r : Fin 4) : 2695 ≤ (Site.scale r).pc ∧ (Site.scale r).pc ≤ 3594 := by
  have := r.isLt; simp only [Site.pc, rowBase]; omega

theorem raw_rowPc (r : Fin 4) (s : Fin 8) :
    2695 ≤ (Site.raw r s).pc ∧ (Site.raw r s).pc ≤ 3594 := by
  have := r.isLt; have := s.isLt; simp only [Site.pc, rowBase]; split_ifs <;> omega

theorem store_rowPc (r : Fin 4) (s : Fin 8) :
    2695 ≤ (Site.store r s).pc ∧ (Site.store r s).pc ≤ 3594 := by
  have := r.isLt; have := s.isLt; simp only [Site.pc, rowBase]; split_ifs <;> omega

theorem quietSrc_pc {x : Site} (h : QuietSrc x) (r : Fin 4) : x.pc ≠ dqScalePc r := by
  have := r.isLt
  cases x with
  | scale _ => exact h.elim
  | raw _ _ => exact h.elim
  | store r' s' =>
    have := r'.isLt
    have : s'.val = 7 := h
    rw [store_pc]; unfold dqStorePc dqScalePc; split_ifs; omega
  | _ => simp only [Site.pc]; unfold dqScalePc; omega

/-- The rows' successor sites. -/
theorem raw_next_done : ∀ r r' : Fin 4, ∀ s i : Fin 8, Done (Control.rawNext r s) r' i →
    r' = r ∧ (i = s ∨ Done (.raw r s) r' i) := by decide +kernel
theorem raw_next_row : ∀ r r' : Fin 4, ∀ s : Fin 8, InRow (Control.rawNext r s) r' →
    r' = r := by decide +kernel
theorem raw_next_scale : ∀ r r' : Fin 4, ∀ s : Fin 8, Control.rawNext r s ≠ .scale r' := by
  decide +kernel
theorem store_next_done : ∀ r r' : Fin 4, ∀ s i : Fin 8,
    Done (Control.storeNext r s) r' i → Done (.store r s) r' i := by decide +kernel
theorem store_next_row : ∀ r r' : Fin 4, ∀ s : Fin 8,
    InRow (Control.storeNext r s) r' → InRow (.store r s) r' := by decide +kernel

/-! ### Control steps keep the element counter off the scale load -/

theorem el_afterA (d : Control.D) : (Control.afterA P d).el = d.el := by
  unfold Control.afterA; rw [apply_ite Control.D.el]; dsimp only; simp only [ite_self]

theorem el_afterSmr (d : Control.D) : (Control.afterSmr P L g d).el = d.el := by
  unfold Control.afterSmr
  rw [apply_ite Control.D.el, apply_ite Control.D.el, el_afterA]
  dsimp only
  simp only [ite_self]

theorem el_loopEntry (d : Control.D) : (Control.loopEntry d).el = d.el := by
  unfold Control.loopEntry; rw [apply_ite Control.D.el]; dsimp only; simp only [ite_self]

theorem el_advance (d : Control.D) : (Control.advance d).el = d.el := by
  unfold Control.advance; rw [apply_ite Control.D.el]; dsimp only; simp only [ite_self]

theorem ctl_el {c c' : Control.D} {e : Event} (h : Control.succ P L g c e = some (some c'))
    (hs : ∀ r, c.site ≠ .scale r) : c'.el = c.el := by
  have hc := fun (x : Control.D) (hx : some (some x) = some (some c')) =>
    Option.some.inj (Option.some.inj hx)
  rcases c with ⟨site⟩
  cases site
  case scale r => exact absurd rfl (hs r)
  case smr => rw [← hc _ h]; exact el_afterSmr _
  case lenA | lenB =>
    simp only [Control.succ] at h
    split at h
    · unfold Code.ncNext at h
      split at h
      · rw [← hc _ h]; try exact el_afterA _
      all_goals cases h
    · cases h
  case wq =>
    simp only [Control.succ] at h
    split at h
    · rw [← hc _ h]; split
      · exact el_loopEntry _
      · rfl
    · cases h
  case wraw | wsv =>
    simp only [Control.succ, Control.poll] at h
    split at h
    · rw [← hc _ h]; split <;> rfl
    · cases h
  case raw =>
    simp only [Control.succ, Control.dataRd] at h
    split at h
    · rw [← hc _ h]
    · cases h
  case store | fpx | arrD | bar => rw [← hc _ h]
  case arrF => rw [← hc _ h]; exact el_advance _
  case exit => cases h

/-! ### The invariant along a step -/

theorem quiet_row {s : Site} (h : Quiet s) (r : Fin 4) (i : Fin 8) :
    InRow s r = false ∧ Done s r i = false := by
  cases s <;> simp_all [Quiet, InRow, Done]

theorem rawOf_word {v : Value} {x : {x // WordOk x}} (h : rawOf v = some x) :
    wordOf 64 v = some x.1 := by
  unfold rawOf at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem scaleWordOf_words {M : List Event} {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32)
    (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32) (h3 : w3 < 2 ^ 32)
    (h : M.map readVal = words [w0, w1, w2, w3]) : scaleWordOf M = scWord w0 w1 w2 w3 := by
  have hw : ∀ f w, w < 2 ^ 32 → readVal f = .bits 32 (BitVec.ofNat 64 w) →
      (readWord 32 f).getD 0 = w := by
    intro f w hw hf
    rw [readWord_eq, hf]
    have : w % 18446744073709551616 = w := Nat.mod_eq_of_lt (by omega)
    have hw' : w < 4294967296 := hw
    simp [wordOf, this, hw']
  have hl : M.length = 4 := by simpa [words] using congrArg List.length h
  rcases M with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, M⟩⟩⟩⟩⟩ <;> simp at hl
  simp only [List.map, words, List.cons.injEq] at h
  obtain ⟨e0, e1, e2, e3, -⟩ := h
  simp only [scaleWordOf, scWord, hw f0 w0 h0 e0, hw f1 w1 h1 e1, hw f2 w2 h2 e2,
    hw f3 w3 h3 e3]

theorem acc_zero {l : List Event} {d' : D} (h0 : d'.c.el = 0) (r : Fin 4) :
    d'.c.el ≤ (atPc l (dqScalePc r)).length ∧
      d'.c.acc = (lastN d'.c.el (atPc l (dqScalePc r))).map readVal := by
  rw [h0]
  exact ⟨Nat.zero_le _, by simp [Control.D.acc, h0, lastN]⟩

/-- **The invariant is kept** by a followed step. -/
theorem invD_step {l : List Event} {d d' : D} {c' : Control.D} {e : Event}
    (hI : InvD l d) (hel : d.c.el < Control.elems d.c.site) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g d.c e = some (some c')) (hd : dataNext d c' e = some d') :
    InvD (l ++ [e]) d' := by
  have hc' := dataNext_c hd
  have hq : QuietSrc d.c.site → InvD (l ++ [e]) d' := fun hq' => by
    have h0 : d'.c.el = 0 := by
      rw [hc', ctl_el hc (fun r h => by rw [h] at hq'; exact hq')]
      cases hs : d.c.site <;> simp_all [Control.elems, QuietSrc]
    refine ⟨fun r _ => acc_zero h0 r, fun r h => ?_, fun r i h => ?_, fun r => ?_,
      fun r _ => by rw [h0]; exact since_zero _ _, fun r h => ?_, fun r i h => ?_⟩
    · rw [hc'] at h; simp [quiet_row (quiet_succ hc hq') r 0] at h
    · rw [hc'] at h; simp [quiet_row (quiet_succ hc hq') r i] at h
    · have hns : d.c.site ≠ .scale r := fun h => by rw [h] at hq'; exact hq'
      have h1 := hI.pos r
      rw [ite0_ne hns] at h1
      rw [atPc_ne (hpc ▸ quietSrc_pc hq' r), h1, h0]
      simp
    · rw [hc'] at h; simp [quiet_row (quiet_succ hc hq') r 0] at h
    · rw [hc'] at h; simp [quiet_row (quiet_succ hc hq') r i] at h
  rcases hs : d.c.site with _ | _ | _ | _ | _ | _ | r | ⟨r, s⟩ | ⟨r, s⟩ | _ | _ | _ | _ | _
  case scale =>
    rw [hs] at hpc hel
    obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .rd a bs := by
      simp only [Control.succ, hs] at hc
      split at hc
      · exact ⟨_, _, ‹_›⟩
      · cases hc
    simp only [Control.succ, hs, hk] at hc
    have hc2 := (Option.some.inj (Option.some.inj hc)).symm
    have hv : loadVal bs = readVal e := by simp [readVal, hk]
    have hL := atPc_eq (l := l) (hpc.trans (scale_pc r))
    have hrow : RowPc e := by show 2695 ≤ e.pc ∧ e.pc ≤ 3594; rw [hpc]; exact scale_rowPc r
    obtain ⟨hle, hacc⟩ := hI.acc r hs
    have hpos := fun r' => hI.pos r'
    have hqs := hI.qsw r hs
    simp only [dataNext, hs, hk] at hd
    by_cases h4 : d.c.el + 1 < 4
    · simp only [Control.scaleNext, h4, ite_true] at hc2
      simp only [h4, ite_true, Option.some.injEq] at hd
      subst hc2 hd
      refine ⟨fun r' h => ?_, fun r' h => ?_, fun r' i h => ?_, fun r' => ?_, fun r' h => ?_,
        fun r' h => by dsimp only at h; rw [hs] at h; simp [InRow] at h,
        fun r' i h => by dsimp only at h; rw [hs] at h; simp [Done] at h⟩
      · dsimp only at h
        rw [hs] at h
        cases (Site.scale.inj h : r = r')
        rw [hL, List.length_append, List.length_singleton, lastN_snoc, List.map_append,
          ← hacc, List.map_singleton, ← hv]
        exact ⟨by dsimp only; omega, by simp [Control.D.acc, loadVal]⟩
      · dsimp only at h; rw [hs] at h; simp [InRow] at h
      · dsimp only at h; rw [hs] at h; simp [Done] at h
      · have h1 := hpos r'
        rw [hs] at h1
        dsimp only
        rw [hs]
        by_cases hr : r = r'
        · subst hr
          rw [hL, List.length_append, List.length_singleton]
          rw [ite0_eq rfl] at h1
          rw [ite0_eq rfl]
          omega
        · have hne : Site.scale r ≠ Site.scale r' := fun h => hr (Site.scale.inj h)
          rw [atPc_ne (fun h => hr (scalePc_inj ((hpc.trans (scale_pc r)).symm.trans h))),
            h1, ite0_ne hne, ite0_ne hne]
      · dsimp only at h; rw [hs] at h
        cases (Site.scale.inj h : r = r')
        exact since_snoc_eq hqs hrow (hpc.trans (scale_pc r))
    · simp only [Control.scaleNext, h4, ite_false] at hc2
      simp only [h4, ite_false] at hd
      obtain ⟨sc0, hsc, rfl⟩ := Option.map_eq_some_iff.mp hd
      subst hc2
      obtain ⟨w0, w1, w2, w3, h0, h1, h2, h3, hw, hs0⟩ := scaleOf_some hsc
      have h3' : d.c.el = 3 := by simp [Control.elems] at hel; omega
      refine ⟨fun r' h => by simp at h, fun r' h => ?_, fun r' i h => by simp [Done] at h,
        fun r' => ?_, fun r' h => by simp at h, fun r' h => ?_,
        fun r' i h => by simp [Done] at h⟩
      · simp only [InRow, decide_eq_true_eq] at h
        subst h
        dsimp only
        rw [hs0, hL, lastN_snoc 3]
        refine (scaleWordOf_words h0 h1 h2 h3 ?_).symm
        rw [List.map_append, ← hw, ← h3', ← hacc, hv]
        rfl
      · have h1 := hpos r'
        rw [hs] at h1
        dsimp only
        have hne : Site.raw r 0 ≠ Site.scale r' := fun h => by cases h
        rw [ite0_ne hne]
        by_cases hr : r = r'
        · subst hr
          rw [hL, List.length_append, List.length_singleton]
          rw [ite0_eq rfl] at h1
          omega
        · have hne' : Site.scale r ≠ Site.scale r' := fun h => hr (Site.scale.inj h)
          rw [atPc_ne (fun h => hr (scalePc_inj ((hpc.trans (scale_pc r)).symm.trans h))),
            h1, ite0_ne hne']
      · simp only [InRow, decide_eq_true_eq] at h
        subst h
        have := since_snoc_eq hqs hrow (hpc.trans (scale_pc r))
        rwa [h3'] at this
  case raw =>
    rw [hs] at hpc hel
    obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .rd a bs := by
      simp only [Control.succ, hs, Control.dataRd] at hc
      split at hc
      · exact ⟨_, _, ‹_›⟩
      · cases hc
    have hc2 : c' = { d.c with site := Control.rawNext r s } := by
      simp only [Control.succ, hs, Control.dataRd, hk] at hc
      exact (Option.some.inj (Option.some.inj hc)).symm
    subst hc2
    simp only [dataNext, hs, hk] at hd
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hd
    have h0 : d.c.el = 0 := by simpa [Control.elems] using hel
    have hrow : RowPc e := by show 2695 ≤ e.pc ∧ e.pc ≤ 3594; rw [hpc]; exact raw_rowPc r s
    have hnsc : ∀ r' : Fin 4, e.pc ≠ dqScalePc r' := fun r' => hpc ▸ raw_ne_scale r r' s
    refine ⟨fun r' _ => acc_zero h0 r', fun r' h => ?_, fun r' i h => ?_, fun r' => ?_,
      fun r' h => absurd h (raw_next_scale r r' s), fun r' h => ?_, fun r' i h => ?_⟩
    · rw [raw_next_row r r' s h, atPc_ne (hpc ▸ raw_ne_scale r r s)]
      exact hI.sc r (by rw [hs]; simp [InRow])
    · obtain ⟨hr, hi | hi⟩ := raw_next_done r r' s i h <;> rw [hr]
      · subst hi
        dsimp only
        rw [Function.update_self, atPc_eq (hpc.trans (raw_pc r i))]
        have hw := rawOf_word hx
        simp only [lastN, List.length_append, List.length_singleton, Nat.add_sub_cancel,
          List.drop_left', rawWordOf, readWord_eq, readVal, hk] at hw ⊢
        rw [hw]; rfl
      · have hne : i ≠ s := by simp [Done] at hi; omega
        dsimp only
        rw [Function.update_of_ne (Fin.val_injective.ne hne),
          atPc_ne (fun h => hne (raw_inj (hpc ▸ h)).2.symm)]
        exact hI.ws r i (by rw [hs]; exact hr ▸ hi)
    · have h1 := hI.pos r'
      rw [hs, ite0_ne (fun h => by cases h)] at h1
      dsimp only
      rw [atPc_ne (hnsc r'), h1, ite0_ne (fun h => raw_next_scale r r' s h)]
    · rw [raw_next_row r r' s h]
      exact since_snoc_ne (hI.qsc r (by rw [hs]; simp [InRow])) hrow (hnsc r)
    · obtain ⟨hr, hi | hi⟩ := raw_next_done r r' s i h <;> rw [hr]
      · subst hi
        exact since_one hrow (hpc.trans (raw_pc r i))
      · have hne : i ≠ s := by simp [Done] at hi; omega
        exact since_snoc_ne (hI.qrw r i (by rw [hs]; exact hr ▸ hi)) hrow
          (fun h => hne (raw_inj (hpc ▸ h)).2.symm)
  case store =>
    rw [hs] at hpc hel
    have hc2 : c' = { d.c with site := Control.storeNext r s } := by
      simp only [Control.succ, hs] at hc
      exact (Option.some.inj (Option.some.inj hc)).symm
    subst hc2
    have hd2 : d' = { d with c := { d.c with site := Control.storeNext r s } } := by
      simp only [dataNext, hs] at hd
      exact (Option.some.inj hd).symm
    subst hd2
    have h0 : d.c.el = 0 := by simpa [Control.elems] using hel
    have hrow : RowPc e := by show 2695 ≤ e.pc ∧ e.pc ≤ 3594; rw [hpc]; exact store_rowPc r s
    refine ⟨fun r' _ => acc_zero h0 r', fun r' h => ?_, fun r' i h => ?_, fun r' => ?_,
      fun r' _ => by dsimp only; rw [h0]; exact since_zero _ _, fun r' h => ?_, fun r' i h => ?_⟩
    · rw [atPc_ne (hpc ▸ store_ne_scale r r' s)]
      exact hI.sc r' (by rw [hs]; exact store_next_row r r' s h)
    · rw [atPc_ne (hpc ▸ store_ne_raw r r' s i)]
      exact hI.ws r' i (by rw [hs]; exact store_next_done r r' s i h)
    · have h1 := hI.pos r'
      rw [hs, ite0_ne (fun h => by cases h)] at h1
      dsimp only
      rw [atPc_ne (hpc ▸ store_ne_scale r r' s), h1, h0]
      simp
    · exact since_snoc_ne (hI.qsc r' (by rw [hs]; exact store_next_row r r' s h)) hrow
        (hpc ▸ store_ne_scale r r' s)
    · exact since_snoc_ne (hI.qrw r' i (by rw [hs]; exact store_next_done r r' s i h)) hrow
        (hpc ▸ store_ne_raw r r' s i)
  all_goals exact hq (by rw [hs]; exact trivial)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
