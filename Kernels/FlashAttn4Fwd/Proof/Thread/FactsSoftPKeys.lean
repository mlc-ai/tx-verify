-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftRegs
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # The keys of the probability stores

Source `p` of the store of probability columns `64 + 16 c …` holds the pack of the
conversions of the probabilities of keys `32 c + 2 p` (low half) and `32 c + 2 p + 1` (high
half) (`SoftmaxTable`). When the scale word, the reference maximum and the words are
single-precision numbers, these are the half-precision values of `p0` in the first tile and of
`p1` in a loop tile (`p0V_read`, `p1V_read`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The conversion of two numbers is the pair of their halves. -/
theorem cvtV_float (a b : ℝ) :
    cvtV (.float .f32 a) (.float .f32 b) = .pair (.float .f16 b) (.float .f16 a) := by
  rw [cvtV, cvtPairE_of_valFloat valFloat_float valFloat_float]
  rfl

/-- Two pairs join to their pair. -/
theorem join_pairs (a b c e : Value) :
    joinValue (.pair a b) (.pair c e) = .pair (.pair a b) (.pair c e) := rfl

/-- A conversion has four bytes: a pair of halves, or the default word. -/
theorem cvtV_cases (a b : Value) : (∃ x y, cvtV a b = .pair x y ∧ x.bytes = 2 ∧ y.bytes = 2) ∨
    cvtV a b = .bits 32 0 := by
  unfold cvtV
  cases h : cvtPairE a b with
  | ok v =>
    obtain ⟨x, y, rfl, hx, hy⟩ := cvtPairE_ok h
    exact .inl ⟨x, y, rfl, hx, hy⟩
  | error e => exact .inr rfl

/-- The halves of the pair of two conversions have four bytes. -/
theorem cvt_split_bytes (a b c e : Value) :
    (splitValue 64 (joinValue (cvtV a b) (cvtV c e))).1.bytes = 4 ∧
      (splitValue 64 (joinValue (cvtV a b) (cvtV c e))).2.bytes = 4 := by
  rcases cvtV_cases a b with ⟨x, y, h1, hx, hy⟩ | h1 <;>
    rcases cvtV_cases c e with ⟨x', y', h2, hx', hy'⟩ | h2 <;> rw [h1, h2]
  · exact ⟨by simp [joinValue, splitValue, Value.bytes, hx, hy],
      by simp [joinValue, splitValue, Value.bytes, hx', hy']⟩
  · exact ⟨by simp [joinValue, splitValue, Value.bytes, hx, hy], rfl⟩
  · exact ⟨rfl, by simp [joinValue, splitValue, Value.bytes, hx', hy']⟩
  · exact ⟨rfl, rfl⟩

variable {L : Launch} {g : Nat} {d : D} {t : TState} {ta : Nat}

/-- The keys of store site `pst false 0`. -/
theorem pst_keys_0 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst false 0) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 0).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p0 L d (32 * 0 + 2 * p))) (.float .f16 (p0 L d (32 * 0 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 0).pc]? = _ := Flow.code_tmemStore_0
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p0V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst false 0` hold four-byte values. -/
theorem pst_bytes_0 {ss : List Opnd} (hs : d.site = .pst false 0) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 0).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 0).pc]? = _ := Flow.code_tmemStore_0
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

/-- The keys of store site `pst false 1`. -/
theorem pst_keys_1 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst false 1) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 1).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p0 L d (32 * 1 + 2 * p))) (.float .f16 (p0 L d (32 * 1 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 1).pc]? = _ := Flow.code_tmemStore_1
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p0V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst false 1` hold four-byte values. -/
theorem pst_bytes_1 {ss : List Opnd} (hs : d.site = .pst false 1) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 1).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 1).pc]? = _ := Flow.code_tmemStore_1
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

/-- The keys of store site `pst false 2`. -/
theorem pst_keys_2 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst false 2) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 2).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p0 L d (32 * 2 + 2 * p))) (.float .f16 (p0 L d (32 * 2 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 2).pc]? = _ := Flow.code_tmemStore_2
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p0V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst false 2` hold four-byte values. -/
theorem pst_bytes_2 {ss : List Opnd} (hs : d.site = .pst false 2) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 2).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 2).pc]? = _ := Flow.code_tmemStore_2
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

/-- The keys of store site `pst false 3`. -/
theorem pst_keys_3 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst false 3) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 3).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p0 L d (32 * 3 + 2 * p))) (.float .f16 (p0 L d (32 * 3 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 3).pc]? = _ := Flow.code_tmemStore_3
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p0V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst false 3` hold four-byte values. -/
theorem pst_bytes_3 {ss : List Opnd} (hs : d.site = .pst false 3) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 3).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst false 3).pc]? = _ := Flow.code_tmemStore_3
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

/-- The keys of store site `pst true 0`. -/
theorem pst_keys_4 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst true 0) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 0).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p1 L d (32 * 0 + 2 * p))) (.float .f16 (p1 L d (32 * 0 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 0).pc]? = _ := Flow.code_tmemStore_4
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p1V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst true 0` hold four-byte values. -/
theorem pst_bytes_4 {ss : List Opnd} (hs : d.site = .pst true 0) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 0).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 0).pc]? = _ := Flow.code_tmemStore_4
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

/-- The keys of store site `pst true 1`. -/
theorem pst_keys_5 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst true 1) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 1).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p1 L d (32 * 1 + 2 * p))) (.float .f16 (p1 L d (32 * 1 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 1).pc]? = _ := Flow.code_tmemStore_5
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p1V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst true 1` hold four-byte values. -/
theorem pst_bytes_5 {ss : List Opnd} (hs : d.site = .pst true 1) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 1).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 1).pc]? = _ := Flow.code_tmemStore_5
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

/-- The keys of store site `pst true 2`. -/
theorem pst_keys_6 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst true 2) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 2).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p1 L d (32 * 2 + 2 * p))) (.float .f16 (p1 L d (32 * 2 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 2).pc]? = _ := Flow.code_tmemStore_6
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p1V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst true 2` hold four-byte values. -/
theorem pst_bytes_6 {ss : List Opnd} (hs : d.site = .pst true 2) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 2).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 2).pc]? = _ := Flow.code_tmemStore_6
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

/-- The keys of store site `pst true 3`. -/
theorem pst_keys_7 {ss : List Opnd} (hsc : ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : WordsF32 d.w) (hs : d.site = .pst true 3) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 3).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (p1 L d (32 * 3 + 2 * p))) (.float .f16 (p1 L d (32 * 3 + 2 * p + 1)))) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 3).pc]? = _ := Flow.code_tmemStore_7
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, rfl, (reg_val h (by table_decide)).trans ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals simp (disch := decide) only [p1V_read hsc hm hwf, cvtV_float, join_pairs,
    split_pair]

/-- The source registers of store site `pst true 3` hold four-byte values. -/
theorem pst_bytes_7 {ss : List Opnd} (hs : d.site = .pst true 3) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 3).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  intro p hp
  have hc' : kernel.code[(Site.pst true 3).pc]? = _ := Flow.code_tmemStore_7
  obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt _ s => s | _ => [])
    (Option.some.inj (hc.symm.trans hc'))
  interval_cases p
  all_goals refine ⟨_, _, rfl, reg_val h (by table_decide), ?_⟩
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first | exact (cvt_split_bytes _ _ _ _).1 | exact (cvt_split_bytes _ _ _ _).2

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
