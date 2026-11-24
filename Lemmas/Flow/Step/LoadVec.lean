-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.Footprint
public meta import Lean

@[expose] public section

/-! # Step combinators for the elements of a vector load

A proof tool, the load counterpart of `step_vec_mid` and `step_vec_last` for a machine that
records the values it reads (as `step_load` does for a scalar load). An element of a vector load
fires a read; when its bytes rebuild into a value `v`, the thread accumulates `v` and stays at the
instruction (`step_ldv_mid`), or, at the last element, writes every destination register with the
accumulated values and continues at the next instruction (`step_ldv_last`). Bytes that do not
rebuild fault the thread; the machine owes `none` there.

The `_sel` forms take the successor as a function `nv` of the value read, so that a machine may
stop on a value of another kind (`some none`, a 32-bit word register that receives something
else), as `step_load_sel` does for a scalar load. `step_load_ext` is the scalar load located by
`accessLoc` (a `.local` load) whose value Core extends (`ld.local.s32` into a 64-bit register):
the machine sees the rebuilt value, the register receives its extension (`extendLoaded`). -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An element of a vector load other than the last: the machine moves to `dok v`, a state at
the same instruction one sub-step later whose accumulator is `d`'s with the value `v` read. -/
theorem step_ldv_mid {d : C.D} {dok : Value → C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hsub : C.sub d + 1 < a.regs.length)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dok v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none)
    (hpc : ∀ v, C.pc (dok v) = C.pc d) (hs : ∀ v, C.sub (dok v) = C.sub d + 1)
    (ha : ∀ v, C.acc (dok v) = C.acc d ++ [v]) (hF : ∀ v, C.facts (dok v) = C.facts d)
    (hinv : ∀ v, C.inv d → C.inv (dok v)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨herr x bs f hv, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    have hm : t.sub + 1 < a.regs.length := by rw [h.2.1]; exact hsub
    have hu : afterLoad t a.regs bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
      simp [afterLoad, hv, hm]
    rw [hu]
    refine .inl (.inr ⟨dok v, _, hok x bs v hv, .refl, ⟨?_, ?_, ?_, h.2.2.2.1, ?_⟩, hinv v hi⟩)
    · exact h.1.trans (hpc v).symm
    · show t.sub + 1 = C.sub (dok v)
      rw [h.2.1, hs]
    · show t.acc ++ [v] = C.acc (dok v)
      rw [h.2.2.1, ha]
    · rw [hF]; exact h.2.2.2.2

/-- The last element of a vector load: the thread writes the destinations `a.regs` with the
accumulated values and `v`, and continues at the next instruction with the facts `F' v`, which
the write establishes from `d`'s facts. -/
theorem step_ldv_last {d : C.D} {dok : Value → C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    {F' : Value → List (Nat × Value)}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hsub : ¬ C.sub d + 1 < a.regs.length)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dok v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none)
    (hF : ∀ (t : TState) v, Holds t.regs (C.facts d) →
      Holds (setRegs t a.regs (C.acc d ++ [v])).regs (F' v))
    (hl : ∀ v, C.Lands d (C.pc d + 1) (F' v) (dok v)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨herr x bs f hv, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    have hm : ¬ t.sub + 1 < a.regs.length := by rw [h.2.1]; exact hsub
    have hu : afterLoad t a.regs bs =
        { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      simp [afterLoad, hv, hm]
    rw [hu]
    have hsk := setRegs_skel t a.regs (t.acc ++ [v])
    refine (hl v).cont hi (hok x bs v hv) ⟨?_, rfl, rfl, ?_, ?_⟩
    · show t.pc + 1 = C.pc d + 1
      rw [h.1]
    · show (setRegs t a.regs (t.acc ++ [v])).fault = none
      rw [hsk.2.2.2]; exact h.2.2.2.1
    · show Holds (setRegs t a.regs (t.acc ++ [v])).regs (F' v)
      rw [h.2.2.1]; exact hF t v h.2.2.2.2

/-- After a load that no direct location rule covers (`locSpace? = none`, as for `.local`) and
without `.nc`, the thread is in `afterAccessLoad t a.ext a.elem.width a.regs bs` for the bytes
read: they are rebuilt and extended as the access says (`extendLoaded`). -/
theorem fires_accessLoad {t u : TState} {a : MemAccess} {pc : Nat} {e : Event}
    (hk : a.kind = .load) (hnc : a.nc = false) (hsp : a.locSpace? = none)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧ u = afterAccessLoad t a.ext a.elem.width a.regs bs := by
  have hnotAtomic : a.rule ≠ some .threadAtomic := by
    rw [MemAccess.rule, hk]
    repeat' split
    all_goals simp_all
  have hacc : Fires pc (accessTmpl A L g t a) e (some u) →
      ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧ u = afterAccessLoad t a.ext a.elem.width a.regs bs := by
    intro hf
    rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, -, -, h⟩ |
      ⟨r, k, hn, -⟩
    · rw [h] at hf
      exact absurd hf.2 (by simp)
    · rw [h] at hf
      obtain ⟨bs, -, rfl, hu⟩ := hf
      exact ⟨_, bs, rfl, Option.some.inj hu⟩
    · simp [hnc] at hn
  simp only [eventTmpl, memTmpl, hsp] at hf
  split at hf
  · simp_all
  · simp_all
  · split at hf
    · exact hacc hf
    · exact absurd hf.2 (by simp)

/-- A value with a bit pattern extends to the extension of its bits. -/
theorem extendLoaded_bits {ext : MemExt} {w n : Nat} {x : BitVec 64} (h : ext ≠ .same) :
    extendLoaded ext w (.bits n x) = .ok (ext.extendBits w x) := by
  cases ext with
  | same => exact absurd rfl h
  | zero _ => simp [extendLoaded, Value.bitPattern, pure, Except.pure]
  | sign _ => simp [extendLoaded, Value.bitPattern, pure, Except.pure]

/-- A scalar load located by `accessLoc` (a `.local` load) into register `r`, whose machine's
successor is a function `nv` of the rebuilt value and whose register receives that value's
extension. A value that does not extend faults the thread; the machine stops there. -/
theorem step_load_ext {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} {r : Nat} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (hsp : a.locSpace? = none)
    (hregs : a.regs = [r])
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hs : C.sub d = 0) (ha : C.acc d = []) (hnn : ∀ v, nv v ≠ none)
    (hext : ∀ v f d', extendLoaded a.ext a.elem.width v = .error f → nv v ≠ some (some d'))
    (hl : ∀ v v' d', nv v = some (some d') → extendLoaded a.ext a.elem.width v = .ok v' →
      C.Lands d (C.pc d + 1) ((r, v') :: dropReg r (C.facts d)) d') :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨x, bs, rfl, rfl⟩ := fires_accessLoad hk hnc hsp hf
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f)
        (by simp [afterAccessLoad, hv, bind, Except.bind])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hn := hok x bs v hv
    rcases hnv : nv v with _ | _ | d'
    · exact absurd hnv (hnn v)
    · exact .inl (.inl (hn.trans hnv))
    · cases hx : extendLoaded a.ext a.elem.width v with
      | error f => exact absurd hnv (hext v f d' hx)
      | ok v' =>
        have hst : afterAccessLoad t a.ext a.elem.width [r] bs = PTX.next (setReg t r v') := by
          have hs0 := h0.2.1
          have ha0 := h0.2.2.1
          cases t
          simp_all [afterAccessLoad, bind, Except.bind, setRegs, PTX.next, setReg]
        rw [hst]
        have h1 : At t (C.pc d) (dropReg r (C.facts d)) := h0.mono (holds_dropReg r h0.2.2.2.2)
        have hr : ∀ q ∈ dropReg r (C.facts d), q.1 ≠ r := fun q hq => by
          simpa using (List.mem_filter.mp hq).2
        exact (hl v v' d' hnv hx).cont hi (hn.trans hnv) (At.set h1 hr)

/-- `step_ldv_mid` with the successor a function `nv` of the value read, which may stop on it. -/
theorem step_ldv_mid_sel {d : C.D} {nv : Value → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hsub : C.sub d + 1 < a.regs.length)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hnn : ∀ v, nv v ≠ none)
    (hmid : ∀ v d', nv v = some (some d') → C.pc d' = C.pc d ∧ C.sub d' = C.sub d + 1 ∧
      C.acc d' = C.acc d ++ [v] ∧ C.facts d' = C.facts d ∧ (C.inv d → C.inv d')) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hn := hok x bs v hv
    rcases hnv : nv v with _ | _ | d'
    · exact absurd hnv (hnn v)
    · exact .inl (.inl (hn.trans hnv))
    · obtain ⟨hpc, hs, ha, hF, hinv⟩ := hmid v d' hnv
      have hm : t.sub + 1 < a.regs.length := by rw [h.2.1]; exact hsub
      have hu : afterLoad t a.regs bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
        simp [afterLoad, hv, hm]
      rw [hu]
      refine .inl (.inr ⟨d', _, hn.trans hnv, .refl, ⟨?_, ?_, ?_, h.2.2.2.1, ?_⟩, hinv hi⟩)
      · exact h.1.trans hpc.symm
      · show t.sub + 1 = C.sub d'
        rw [h.2.1, hs]
      · show t.acc ++ [v] = C.acc d'
        rw [h.2.2.1, ha]
      · rw [hF]; exact h.2.2.2.2

/-- The facts after a load into the registers `rs` of the values `vs`: each destination's value,
then the facts `F` of the other registers. -/
def vecFacts : List Nat → List Value → List (Nat × Value) → List (Nat × Value)
  | r :: rs, v :: vs, F => (r, v) :: vecFacts rs vs (dropReg r F)
  | _, _, F => F

theorem holds_vecFacts : ∀ {rs : List Nat} {vs : List Value} {t : TState}
    {F : List (Nat × Value)}, rs.Nodup → Holds t.regs F →
    Holds (setRegs t rs vs).regs (vecFacts rs vs F)
  | [], _, _, _, _, h => h
  | _ :: _, [], _, _, _, h => h
  | r :: rs, v :: vs, t, F, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    have h1 : Holds (setReg t r v).regs (dropReg r F) :=
      holds_update (holds_dropReg r h) fun q hq => by simpa using (List.mem_filter.mp hq).2
    refine ⟨?_, holds_vecFacts hnd'.2 h1⟩
    show (setRegs (setReg t r v) rs vs).regs r = some v
    rw [setRegs_other _ _ _ _ hnd'.1]
    simp [setReg]

/-- `step_ldv_last` with the successor a function `nv` of the value read, which may stop on it;
the facts after the load are `vecFacts` of the destinations. -/
theorem step_ldv_last_sel {d : C.D} {nv : Value → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hsub : ¬ C.sub d + 1 < a.regs.length) (hnd : a.regs.Nodup)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hnn : ∀ v, nv v ≠ none)
    (hl : ∀ v d', nv v = some (some d') →
      C.Lands d (C.pc d + 1) (vecFacts a.regs (C.acc d ++ [v]) (C.facts d)) d') :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hn := hok x bs v hv
    rcases hnv : nv v with _ | _ | d'
    · exact absurd hnv (hnn v)
    · exact .inl (.inl (hn.trans hnv))
    · have hm : ¬ t.sub + 1 < a.regs.length := by rw [h.2.1]; exact hsub
      have hu : afterLoad t a.regs bs =
          { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
        simp [afterLoad, hv, hm]
      rw [hu]
      have hsk := setRegs_skel t a.regs (t.acc ++ [v])
      refine (hl v d' hnv).cont hi (hn.trans hnv) ⟨?_, rfl, rfl, ?_, ?_⟩
      · show t.pc + 1 = C.pc d + 1
        rw [h.1]
      · show (setRegs t a.regs (t.acc ++ [v])).fault = none
        rw [hsk.2.2.2]; exact h.2.2.2.1
      · show Holds (setRegs t a.regs (t.acc ++ [v])).regs _
        rw [h.2.2.1]; exact holds_vecFacts hnd h.2.2.2.2

end

open Lean Meta Elab Tactic

/-- The elements of a list that evaluates to a literal list. -/
meta partial def listElems (l : Expr) : MetaM (Option (List Expr)) := do
  let l ← whnfD l
  if l.isAppOfArity ``List.nil 1 then return some []
  unless l.isAppOfArity ``List.cons 3 do return none
  let some rest ← listElems (l.getArg! 2) | return none
  return some (l.getArg! 1 :: rest)

/-- `vec_facts_norm`: write the facts `vecFacts rs vs F` of a vector load (`step_ldv_last_sel`)
whose destinations and values evaluate to literal lists as `(r₀, v₀) :: … :: dropReg … F`, the
form `drop_norm` and `seg_fp` read. -/
elab "vec_facts_norm" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ty' ← Meta.transform ty (pre := fun e => do
    unless e.isAppOfArity ``PTX.Flow.Code.vecFacts 3 do return .continue
    let rs ← PTX.Flow.regList (e.getArg! 0)
    let some vs ← listElems (e.getArg! 1) | return .continue
    let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``PTX.Value]
    let mut cells := #[]
    let mut F := e.getArg! 2
    for (r, v) in rs.toList.zip vs do
      cells := cells.push (← mkAppM ``Prod.mk #[mkNatLit r, v])
      F ← mkAppM ``PTX.Flow.Code.dropReg #[mkNatLit r, F]
    let out := cells.foldr (fun c acc => mkApp3 (mkConst ``List.cons [.zero]) pairTy c acc) F
    return .done out)
  if ty' != ty then replaceMainGoal [← goal.change ty']

end PTX.Flow.Code
