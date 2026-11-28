-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedDeclI
public import Lemmas.Flow.TypedPackF
public import Lemmas.Flow.TypedSingleF

@[expose] public section

/-! # One local instruction whose outcome a caller proves, as a piece of a typed window

`singleNeeds op` reads the instruction `op` as one of the single pieces of the late data lanes
(`add`, `sub`, `mul` of one lane or `add`, `mul` of two, `neg.f32`, `lg2.approx.ftz.f32`, the pack
`cvt.rn.bf16x2.f32`): the tags its operands must have, the register it writes, and the tag of the
datum it writes. `SingleStep` is what a kernel proves once for a pc (the step succeeds from a state
of the needed tags and writes the datum), `segQ_single` the strict piece it gives, to be composed
with the typed runs of a generated window. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- What a single piece needs, the register it writes and the tag of that register. -/
abbrev Single := EnvF × Nat × TagF

/-- A register operand must hold a datum. -/
def needOf : Opnd → EnvF
  | .reg r => [(r, .dat32)]
  | _ => []

/-- `add`, `sub`, `mul` of one lane. -/
def scalarN (f : FloatInstr) (d : Nat) (a b : Opnd) : Option Single :=
  if (f.op = .add ∨ f.op = .sub ∨ f.op = .mul) ∧
      f = { op := f.op, ty := ty1 .f32, ftz := f.ftz, dsts := [some d], srcs := [a, b] } ∧
      d32o (needOf a ++ needOf b) a = true ∧ d32o (needOf a ++ needOf b) b = true then
    some (needOf a ++ needOf b, d, .dat32)
  else none

/-- `add`, `mul` of two lanes. -/
def pairN (f : FloatInstr) (d : Nat) : Opnd → Opnd → Option Single
  | .reg x, .reg y =>
    if (f.op = .add ∨ f.op = .mul) ∧
        f = { op := f.op, ty := ⟨.f32, 2⟩, dsts := [some d], srcs := [.reg x, .reg y] } then
      some ([(x, .dat64), (y, .dat64)], d, .dat64)
    else none
  | _, _ => none

/-- `neg.f32` and `lg2.approx.ftz.f32`. -/
def unaryN (f : FloatInstr) (d : Nat) (a : Opnd) : Option Single :=
  if (f = { negI false with dsts := [some d], srcs := [a] } ∨
      f = { lg2I true with dsts := [some d], srcs := [a] }) ∧ d32o (needOf a) a = true then
    some (needOf a, d, .dat32)
  else none

/-- The pack `cvt.rn.bf16x2.f32` of two registers. -/
def packN (c : CvtInstr) : Option Single :=
  match c.srcs with
  | [.reg _, .reg _] =>
    if c.dst = .packed (.float .bf16) 2 ∧ c.src = .float .f32 ∧ c.rnd = some .rn ∧
        c.plain = true then some ([], c.d, .dat32)
    else none
  | _ => none

/-- The single floating pieces. -/
def floatN (f : FloatInstr) : Option Single :=
  match f.dsts, f.srcs with
  | [some d], [a, b] => (scalarN f d a b).or (pairN f d a b)
  | [some d], [a] => unaryN f d a
  | _, _ => none

/-- The single pieces. -/
def singleNeeds : Op → Option Single
  | .float f => floatN f
  | .cvt c => packN c
  | _ => none

/-- The shapes `singleNeeds` finds. -/
inductive IsSingle : Op → Single → Prop
  | scalar (o : FOp) (fz : Bool) (d : Nat) (a b : Opnd) :
      (o = .add ∨ o = .sub ∨ o = .mul) → d32o (needOf a ++ needOf b) a = true →
      d32o (needOf a ++ needOf b) b = true →
      IsSingle (scalarOp o fz d a b) (needOf a ++ needOf b, d, .dat32)
  | pair (o : FOp) (d x y : Nat) : (o = .add ∨ o = .mul) →
      IsSingle (pairOp o d x y) ([(x, .dat64), (y, .dat64)], d, .dat64)
  | neg (d : Nat) (a : Opnd) : d32o (needOf a) a = true →
      IsSingle (.float { negI false with dsts := [some d], srcs := [a] }) (needOf a, d, .dat32)
  | lg2 (d : Nat) (a : Opnd) : d32o (needOf a) a = true →
      IsSingle (.float { lg2I true with dsts := [some d], srcs := [a] }) (needOf a, d, .dat32)
  | pack (c : CvtInstr) (a b : Nat) : c.srcs = [.reg a, .reg b] →
      c.dst = .packed (.float .bf16) 2 → c.src = .float .f32 → c.rnd = some .rn →
      c.plain = true → IsSingle (.cvt c) ([], c.d, .dat32)

theorem scalarN_sound {f : FloatInstr} {d : Nat} {a b : Opnd} {nd : Single}
    (h : scalarN f d a b = some nd) : IsSingle (.float f) nd := by
  unfold scalarN at h
  split_ifs at h with hc
  obtain ⟨ho, hf, ha, hb⟩ := hc
  cases h
  rw [hf]
  exact IsSingle.scalar _ _ d a b ho ha hb

theorem pairN_sound {f : FloatInstr} {d : Nat} {a b : Opnd} {nd : Single}
    (h : pairN f d a b = some nd) : IsSingle (.float f) nd := by
  cases a <;> cases b <;> simp only [pairN] at h <;> try (cases h)
  split_ifs at h with hc
  obtain ⟨ho, hf⟩ := hc
  cases h
  rw [hf]
  exact IsSingle.pair _ d _ _ ho

theorem unaryN_sound {f : FloatInstr} {d : Nat} {a : Opnd} {nd : Single}
    (h : unaryN f d a = some nd) : IsSingle (.float f) nd := by
  unfold unaryN at h
  split_ifs at h with hc
  obtain ⟨hf | hf, hd⟩ := hc <;> cases h <;> rw [hf]
  · exact IsSingle.neg d a hd
  · exact IsSingle.lg2 d a hd

theorem packN_sound {c : CvtInstr} {nd : Single} (h : packN c = some nd) :
    IsSingle (.cvt c) nd := by
  unfold packN at h
  split at h
  · rename_i x y hs
    split_ifs at h with hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    cases h
    exact IsSingle.pack _ x y hs h1 h2 h3 h4
  · cases h

theorem floatN_sound {f : FloatInstr} {nd : Single} (h : floatN f = some nd) :
    IsSingle (.float f) nd := by
  unfold floatN at h
  split at h
  · rename_i d a b _ _
    rcases hs : scalarN f d a b with _ | s
    · rw [hs, Option.none_or] at h
      exact pairN_sound h
    · rw [hs, Option.some_or] at h
      cases h
      exact scalarN_sound hs
  · exact unaryN_sound h
  · cases h

theorem singleNeeds_sound {op : Op} {nd : Single} (h : singleNeeds op = some nd) :
    IsSingle op nd := by
  cases op with
  | float f => exact floatN_sound h
  | cvt c => exact packN_sound h
  | _ => simp [singleNeeds] at h

/-- Each need is served by the tag the window holds at the pc. -/
def needsIn (nd e : EnvF) : Bool := nd.all fun p => TagF.sat (e.lookup p.1) p.2

theorem typedF_of_needs {nd e : EnvF} {t : TState} (h : needsIn nd e = true) (ht : TypedF e t) :
    TypedF nd t := by
  intro r tg hr
  simp only [needsIn, List.all_eq_true] at h
  exact TagF.sat_ok (v := t.regs r) (need := tg) (h := e.lookup r) (h _ (lookup_mem' hr))
    (fun tg' h' => ht r tg' h')

/-- **What a kernel proves of a single pc**: from a state of the needed tags that the fact `R`
covers, the instruction steps to the next pc with the datum written. -/
def SingleStep (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (R : TState → Prop)
    (pc : Nat) : Prop :=
  ∀ op nd, K.code[pc]? = some ⟨none, op⟩ → singleNeeds op = some nd → ∀ t : TState,
    t.pc = pc → TypedF nd.1 t → R t →
    ∃ v, execLocalA A L g t op = .ok (PTX.next (setReg t nd.2.1 v)) ∧ nd.2.2.ok (some v)

/-- The check of a window at a single pc: the instruction is one, with the needs held and the
datum tagged at the next pc, and it writes `d`. -/
def singleOk (op : Op) (qt : Nat → EnvF) (pc d : Nat) : Bool :=
  match singleNeeds op with
  | some nd => op.isLocal && needsIn nd.1 (qt pc) && afterF qt pc [(nd.2.1, nd.2.2)] &&
      decide (nd.2.1 = d)
  | none => false

/-- **A single piece is a strict segment** under the tags and the fact `R` of the states the lane
reaches. -/
theorem segQ_single {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {op : Op}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hk : singleOk op qt pc d = true) (hS : SingleStep K A L g R pc) (hG : ∀ p ∈ G, p ∈ F)
    (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G := by
  unfold singleOk at hk
  split at hk
  · rename_i nd hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨⟨⟨hl, hN⟩, hq⟩, rfl⟩ := hk
    exact segQ_decl hc hl (fun t hty hp hr =>
      hS op nd hc hn t hp (typedF_of_needs hN hty) hr) hq hG hd
  · cases hk

/-- **A guarded branch** after a strict segment under the tags and `TauAll R`. -/
theorem SegQT.bra {qt : Nat → EnvF} {R : TState → Prop} {a pc p target : Nat} {uni : Bool}
    {F G : List (Nat × Value)} (pick : Bool)
    (h1 : SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) a F pc G)
    (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hL : ∀ t x, x ∈ A → x.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsInF (qt (if pick then target else pc + 1)) (qt pc) = true)
    (hp : ∀ u, At u pc G → QTF qt u → u.regs p = some (.pred pick)) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) a F
      (if pick then target else pc + 1) G := by
  intro t ht hq0
  obtain ⟨u, hr, hu, hQ, hT⟩ := h1 t ht hq0
  obtain ⟨v, hl, hregs, hv⟩ := Havoc.run_bra_regs hc pick hu (hp u hu hQ) (hL u) hA
  have hr' := hr.trans (run_rtg hl)
  refine ⟨v, hr', hv, ?_, fun w hw => hT w ((run_rtg hl).trans hw)⟩
  have hQ' : TypedF (qt pc) u := by simpa [QTF, hu.1] using hQ
  have : TypedF (qt (if pick then target else pc + 1)) v := by
    intro r tg hr''
    rw [hregs]
    exact typedF_of_tagsIn hq hQ' r tg hr''
  simpa [QTF, hv.1] using this

end
end PTX.Flow.TyG
