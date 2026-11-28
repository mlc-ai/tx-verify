-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedSingleG
public import Lemmas.Flow.TypedAllF

@[expose] public section

/-! # Pieces whose results carry no tag: the bias path

The pack of two 16-bit halves into a word, the unpack of a word and the widening
`cvt.f32.bf16` of a half read registers a bias load wrote: a bf16 number (`.float .bf16 _`), which
no tag describes. A piece of this kind (`HalfStep`) has no needs in the table; the registers it
writes are not in the table (`segQ_halfD`), except the widened datum (`.dat32`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc PTX.Assumption

noncomputable section

/-- A half: a 16-bit pattern or a bf16 number. -/
def Half16 (v : Value) : Prop := (∃ x, v = .bits 16 x) ∨ ∃ x, v = .float .bf16 x

/-- A word of two halves: 32 bits, or a pair of halves. -/
def Word32 (v : Value) : Prop :=
  (∃ x, v = .bits 32 x) ∨ ∃ lo hi, v = .pair lo hi ∧ Half16 lo ∧ Half16 hi

/-- The registers an instruction of the bias path writes: the tagged and the untagged ones. -/
def halfOuts : Op → Option (EnvF × List Nat)
  | .move m => match m.kind, m.ty, m.dsts, m.srcs with
    | .pack, .int _ 32, [some d], [.reg _, .reg _] =>
      if m.rule == some .threadMove then some ([], [d]) else none
    | .unpack, .int _ 32, [some lo, some hi], [.reg _] =>
      if m.rule == some .threadMove then some ([], [lo, hi]) else none
    | _, _, _, _ => none
  | .cvt c => match c.srcs with
    | [.reg r] => if decide (c = widenBfC c.d (.reg r)) then some ([(c.d, .dat32)], []) else none
    | _ => none
  | _ => none

/-- What a source register of the instruction holds. -/
def halfSrcOk : Op → Value → Prop
  | .move ⟨.unpack, _, _, _⟩ => Word32
  | _ => Half16

/-- The source registers of the instruction. -/
def halfRegs : Op → List Nat
  | .move m => m.srcs.filterMap fun o => match o with | .reg r => some r | _ => none
  | .cvt c => c.srcs.filterMap fun o => match o with | .reg r => some r | _ => none
  | _ => []

/-- **What a kernel proves of a pc of the bias path**: from a state the fact `R` covers, the step
succeeds, writes the listed registers (`outs` with their tags, `W` without) and moves on. -/
def HalfStep (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (R : TState → Prop)
    (pc : Nat) (outs : EnvF) (W : List Nat) : Prop :=
  ∀ op, K.code[pc]? = some ⟨none, op⟩ → ∀ t : TState, t.pc = pc → R t →
    ∃ u, execLocalA A L g t op = .ok u ∧ u.pc = pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      u.fault = t.fault ∧ (∀ r, r ∉ outs.map Prod.fst ++ W → u.regs r = t.regs r) ∧
      ∀ p ∈ outs, p.2.ok (u.regs p.1)

/-- The tags at `pc + 1` are those of the registers a piece writes with a tag or already held at
`pc`, and none of the untagged registers `W`. -/
def afterW (qt : Nat → EnvF) (pc : Nat) (outs : EnvF) (W : List Nat) : Bool :=
  (qt (pc + 1)).all fun p => !W.contains p.1 && TagF.sat ((outs ++ qt pc).lookup p.1) p.2

/-- `HalfStep` at a pc for the registers `o` (tagged, untagged). -/
abbrev HalfStepO (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (R : TState → Prop)
    (pc : Nat) (o : EnvF × List Nat) : Prop :=
  HalfStep K A L g R pc o.1 o.2

theorem typedF_afterW {e e' : EnvF} {t u : TState} {outs : EnvF} {W : List Nat}
    (ht : TypedF e t) (hw : ∀ r, r ∉ outs.map Prod.fst ++ W → u.regs r = t.regs r)
    (hv : ∀ p ∈ outs, p.2.ok (u.regs p.1))
    (h : e'.all (fun p => !W.contains p.1 && TagF.sat ((outs ++ e).lookup p.1) p.2) = true) :
    TypedF e' u := by
  intro r tg hr
  have h1 := (List.all_eq_true.mp h) (r, tg) (lookup_mem' hr)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  refine TagF.sat_ok (v := u.regs r) (need := tg) (h := (outs ++ e).lookup r) h1.2 fun tg' h' => ?_
  rcases lookup_append_some h' with h2 | ⟨h2, h3⟩
  · exact hv _ (by simpa using lookup_mem' h2)
  · have hW : r ∉ W := fun hm =>
      Bool.false_ne_true (h1.1.symm.trans (List.contains_iff_mem.mpr hm))
    rw [hw r (by simp [lookup_none_keys h2, hW])]
    exact ht r tg' h3

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The table in front of the old one, the untagged registers not in it. -/
theorem typedF_consW {e : EnvF} {t u : TState} {outs : EnvF} {W : List Nat}
    (ht : TypedF e t) (hw : ∀ r, r ∉ outs.map Prod.fst ++ W → u.regs r = t.regs r)
    (hv : ∀ p ∈ outs, p.2.ok (u.regs p.1)) (hf : W.all (fun w => e.lookup w == none) = true) :
    TypedF (outs ++ e) u := by
  intro r tg h
  rcases lookup_append_some h with h1 | ⟨h1, h2⟩
  · exact hv _ (by simpa using lookup_mem' h1)
  · have hW : r ∉ W := fun hm => by
      have := (List.all_eq_true.mp hf) r hm
      simp [h2] at this
    rw [hw r (by simp [lookup_none_keys h1, hW])]
    exact ht r tg h2

/-- **A piece of the bias path is a strict segment** when its end table follows from the typed
state: the registers outside `outs` and `W` keep their values. -/
theorem segQ_halfG {qt : Nat → EnvF} {R : TState → Prop} {pc : Nat} {op : Op} {outs : EnvF}
    {W : List Nat} {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true)
    (hq : ∀ t u : TState, TypedF (qt pc) t → (∀ r, r ∉ outs.map Prod.fst ++ W → u.regs r = t.regs r)
      → (∀ p ∈ outs, p.2.ok (u.regs p.1)) → TypedF (qt (pc + 1)) u)
    (hS : HalfStep K A L g R pc outs W) (hG : ∀ p ∈ G, p ∈ F)
    (hd : ∀ p ∈ G, p.1 ∉ outs.map Prod.fst ++ W) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G := by
  refine SegQ.local1 hc hl hG fun t ht ⟨hQ, hT⟩ => ?_
  have hty : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  obtain ⟨u, hex, hpc, hsub, hacc, hfl, hw, hv⟩ := hS op hc t ht.1 (hT t .refl)
  refine ⟨u, hex, hpc, hsub, hacc, hfl, fun p hp => hw p.1 (hd p hp), fun hu => ⟨?_, fun w hw' =>
    hT w (.head hu hw')⟩⟩
  unfold QTF
  rw [hpc]
  exact hq t u hty hw hv

/-- The end table has its own entries checked (`afterW`). -/
theorem segQ_halfD {qt : Nat → EnvF} {R : TState → Prop} {pc : Nat} {op : Op} {outs : EnvF}
    {W : List Nat} {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (hq : afterW qt pc outs W = true)
    (hS : HalfStep K A L g R pc outs W) (hG : ∀ p ∈ G, p ∈ F)
    (hd : ∀ p ∈ G, p.1 ∉ outs.map Prod.fst ++ W) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G :=
  segQ_halfG hc hl (fun _ _ ht hw hv => typedF_afterW ht hw hv hq) hS hG hd

/-- The end table is the old one with the tagged results in front (`rfl`). -/
theorem segQ_halfE {qt : Nat → EnvF} {R : TState → Prop} {pc : Nat} {op : Op} {outs : EnvF}
    {W : List Nat} {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (hq : qt (pc + 1) = outs ++ qt pc)
    (hf : W.all (fun w => (qt pc).lookup w == none) = true)
    (hS : HalfStep K A L g R pc outs W) (hG : ∀ p ∈ G, p ∈ F)
    (hd : ∀ p ∈ G, p.1 ∉ outs.map Prod.fst ++ W) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G :=
  segQ_halfG hc hl (fun _ _ ht hw hv => hq ▸ typedF_consW ht hw hv hf) hS hG hd

theorem bytes_half {v : Value} (h : Half16 v) : v.bytes = 2 := by
  rcases h with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rfl

theorem exec_packH {t : TState} {k : IType} {d a b : Nat} {x y : Value}
    (hx : t.regs a = some x) (hy : t.regs b = some y) (h1 : x.bytes = 2) (h2 : y.bytes = 2) :
    execMove L g t (.move ⟨.pack, .int k 32, [some d], [.reg a, .reg b]⟩) =
      .ok (next (setReg t d (joinValue x y))) := by
  simp [execMove, readValue, readReg, hx, hy, h1, h2, DType.width, bind, Except.bind, pure,
    Except.pure]

theorem split_word {v : Value} (h : Word32 v) :
    v.bytes = 4 ∧ (splitValue 32 v).1.bytes = 2 ∧ (splitValue 32 v).2.bytes = 2 := by
  rcases h with ⟨x, rfl⟩ | ⟨lo, hi, rfl, h1, h2⟩
  · exact ⟨rfl, by simp [splitValue, Value.bytes], by simp [splitValue, Value.bytes]⟩
  · simp [splitValue, Value.bytes, bytes_half h1, bytes_half h2]

/-- **The bias path's moves and widening are steps**, from the facts about their sources. -/
theorem half_step {R : TState → Prop} {pc : Nat} {outs : EnvF} {W : List Nat}
    (ho : ∀ op, K.code[pc]? = some ⟨none, op⟩ → halfOuts op = some (outs, W))
    (hN : PlainShape A L g pc (pc + 1)) (hS : PlainSegs A pc (pc + 1))
    (hD : WidenRules A L g pc (pc + 1))
    (hR : ∀ op, K.code[pc]? = some ⟨none, op⟩ → ∀ t : TState, t.pc = pc → R t →
      ∀ r ∈ halfRegs op, ∃ v, t.regs r = some v ∧ halfSrcOk op v) :
    HalfStep K A L g R pc outs W := by
  intro op hc t hpc hRt
  have ho' := ho op hc
  have hr := hR op hc t hpc hRt
  have hp1 : pc ≤ t.pc := hpc ▸ le_rfl
  have hp2 : t.pc < pc + 1 := by omega
  cases op with
  | move m =>
    rcases m with ⟨kind, ty, dsts, srcs⟩
    unfold halfOuts at ho'
    simp only at ho'
    split at ho'
    · rename_i k d a b
      split_ifs at ho' with hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ho')
      obtain ⟨x, hxr, hxh⟩ := hr a (by simp [halfRegs])
      obtain ⟨y, hyr, hyh⟩ := hr b (by simp [halfRegs])
      have hex := execLocalA_plain hN hS hp1 hp2
        (op := .move ⟨.pack, .int k 32, [some d], [.reg a, .reg b]⟩) (.inr (.inl ⟨_, rfl⟩))
      rw [execLocal_move (beq_iff_eq.mp hm), exec_packH hxr hyr (bytes_half hxh)
        (bytes_half hyh)] at hex
      refine ⟨_, hex, by simp [next, setReg, hpc], rfl, rfl, rfl, fun r hr' => ?_, by simp⟩
      simp only [List.map_nil, List.nil_append, List.mem_singleton] at hr'
      simp [next, setReg, Function.update_of_ne hr']
    · rename_i k lo hi a
      split_ifs at ho' with hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ho')
      obtain ⟨v, hv, hw⟩ := hr a (by simp [halfRegs])
      obtain ⟨hb, h1, h2⟩ := split_word (v := v) hw
      have hex := execLocalA_plain hN hS hp1 hp2
        (op := .move ⟨.unpack, .int k 32, [some lo, some hi], [.reg a]⟩) (.inr (.inl ⟨_, rfl⟩))
      rw [execLocal_move (beq_iff_eq.mp hm), exec_unpack hv hb h1 h2] at hex
      refine ⟨_, hex, by simp [next, setReg, hpc], rfl, rfl, rfl, fun r hr' => ?_, by simp⟩
      simp only [List.map_nil, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hr'
      show (setReg (setReg t lo _) hi _).regs r = t.regs r
      rw [regs_two]
      simp [hr'.1, hr'.2]
    · simp at ho'
  | cvt c =>
    simp only [halfOuts] at ho'
    split at ho'
    · rename_i ss r hss
      split_ifs at ho' with hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ho')
      simp only [decide_eq_true_eq] at hm
      generalize c.d = d at *
      subst hm
      obtain ⟨v, hv, hw⟩ := hr r (by simp [halfRegs])
      rcases (hw : Half16 v) with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨u, hex, hu1, hu2, hu3, hu4, hu5, hu6⟩ := absWiden_sound hD
          [(r, .old (.bits 16))] (.cvt (widenBfC d (.reg r))) [(d, .dat32)] t
          (by simp [absWiden]) hp1 hp2 (fun r' tg h => by
            by_cases e : (r' == r) = true
            · obtain rfl := beq_iff_eq.mp e
              simp only [List.lookup, e, Option.some.injEq] at h
              subst h
              exact ⟨x, hv⟩
            · simp [List.lookup, e] at h)
        exact ⟨u, hex, by omega, hu2, hu3, hu4, by simpa using hu5, hu6⟩
      · have hrd : readERealOpnd t .bf16 (.reg r) = some (pure (y : EReal)) := by
          rw [readERealOpnd_reg hv]; simp [readEReal]
        obtain ⟨hI, -⟩ := hD t hp1 hp2 d r
        have hex := hI (pure (next (setReg t d (erealValue .f32 y))))
          (by simp only [execWidenBf, hrd, bindRead]; rfl)
        refine ⟨_, hex, by simp [next, setReg, hpc], rfl, rfl, rfl, fun r' hr' => ?_, ?_⟩
        · simp only [List.map_cons, List.map_nil, List.append_nil, List.mem_singleton] at hr'
          simp [next, setReg, Function.update_of_ne hr']
        · intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨_, by simp [next, setReg], dat32_erealValue (y : EReal)⟩
    · simp at ho'
  | _ => simp [halfOuts] at ho'

end
end PTX.Flow.TyG
