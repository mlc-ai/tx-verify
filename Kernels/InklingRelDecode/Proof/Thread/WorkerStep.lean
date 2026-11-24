-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Worker
public import Lemmas.Flow.Step.RuleStep

@[expose] public section

/-! # What the worker's steps need, and the steps `site_cases` does not discharge

The conclusion of a step (`Step`), the segments (`SegTo`), the evaluation of a segment
(`wk_seg`, and `wk_seg_site` for `site_cases`), and the two sites whose steps are written out:
the shuffle of the warp index (the branch after it reads the received word's comparison with 4,
which the evaluation does not decide) and the load of the role byte (a zero-extending load,
`ld.shared.u8`, whose successor the machine computes from the byte, `dispatch`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- The conclusion of a step of this machine: it leaves the machine, or steps to `d'` at `t'` by
a run of `Tau`, or the event is a fault and the thread is dead. -/
def Step (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  (next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
      Inv L g d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-- A segment of the worker's code from `pc` with facts `F` to the site of `d'`. -/
abbrev SegTo (L : Launch) (g pc : Nat) (F : List (Nat × Value)) (d' : D) : Prop :=
  ∃ k, Seg kernel asms L g k pc F d'.site.pc (facts L g d')

/-- The invariant does not depend on the site. -/
theorem Inv.at {s : Site} (hi : Inv L g d) : Inv L g ⟨s, d.P⟩ :=
  ⟨hi.warp, hi.tid, hi.pins⟩

theorem facts_ne {pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- A table fact at a checkpoint where the register is live. -/
theorem tbl_mem {pc : Nat} {d : D} {r : Nat} {v : Value} (hl : r ∈ Flow.live pc)
    (hv : valueOf L g d r = v) : (r, v) ∈ factsAt L g pc d :=
  hv ▸ Flow.mem_factsFrom hl

/-- Facts at a program counter, restated at another whose live registers are among them. -/
theorem holds_relive {pc pc' : Nat} {d d' : D} {R : Nat → Option Value}
    (h : Holds R (factsAt L g pc d)) (hv : valueOf L g d' = valueOf L g d)
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) : Holds R (factsAt L g pc' d') := by
  unfold factsAt at h ⊢
  rw [hv]
  exact holds_factsFrom_mono h hl

/-- A segment of the worker as a step. -/
theorem step_of_seg {d' : D} {F : List (Nat × Value)} {pc : Nat}
    (hn : next L g d e = some (some d')) (hi : Inv L g d') (hu : At u pc F)
    (hs : SegTo L g pc F d') : Step L g d e u := by
  obtain ⟨k, hs⟩ := hs
  obtain ⟨t', hr, ht'⟩ := hs u hu
  exact .inl (.inr ⟨d', t', hn, run_rtg hr, ht', hi⟩)

theorem Inv.setTm (hi : Inv L g d) (s : Site) (v : Value) : Inv L g ⟨s, setTm d.P v⟩ :=
  ⟨hi.warp, hi.tid, hi.pins.setTm v⟩

/-! ### Evaluating a segment -/

/-- No assumption of the kernel selects a segment at a program counter outside the software
`exp2` instances, and none has a local rule for a branch (the loader's lemmas). -/
theorem asms_localRule_bra {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none :=
  Loader.asms_localRule_bra

theorem asms_segFreePc {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc asms pc :=
  Loader.asms_segFreePc h

/-- The table's values at a state, evaluated. -/
macro "wk_values" : tactic =>
  `(tactic| simp only [valueOf, own, Pro.val, Pro.table, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none, Loader.natOf_b32, Loader.natOf64_b64, Nat.reduceEqDiff, ↓reduceIte])

/-- Close one equation between a computed and a stated register value. -/
syntax "wk_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wk_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | (dsimp only [Loader.baseW, Loader.addW, Loader.rdW]
         all_goals (try simp only [kind_s_beq_s, kind_u_beq_s, kind_b_beq_s, ↓reduceIte]))
      | (simp only [Value.pred.injEq, $extra,*]
         nf_simp [PTX.compare, decide_eq_decide, ne_eq, decide_eq_false_iff_not]
         omega)
      | seg_close [Loader.natOf_b32, Loader.natOf64_b64, $extra,*]
      | (nf_simp [intBits, intOf, toSigned, Loader.natOf_b32, Loader.natOf64_b64, $extra,*]
         all_goals (try split_ifs)
         all_goals omega))

/-- Evaluate a segment of the worker from `h` and close the facts of its end state. -/
syntax "wk_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wk_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
        try simp only [valueOf, own, Pro.val, Pro.table, PTX.Flow.lookupLit, Option.getD_some,
          Option.getD_none, Loader.natOf_b32, Loader.natOf64_b64, Nat.reduceEqDiff,
          ↓reduceIte, $extra,*]
        all_goals wk_close [$extra,*])

/-- The register `%p3` of a thread in warp 4 or above is false. -/
theorem p3_false (hw : 4 ≤ warpOf L g) : decide (g % L.block < 32) = false := by
  simp only [warpOf] at hw
  simp
  omega

/-- `%p3` (false in the worker's warps) in front of the start facts of a segment. -/
theorem seg_p3 {n s b : Nat} {F G : List (Nat × Value)} {c : Bool}
    (hp : (3, Value.pred c) ∈ F) (hc : c = false)
    (h : Seg kernel asms L g n s ((3, .pred false) :: F) b G) : Seg kernel asms L g n s F b G :=
  h.weaken_start fun _ hR => ⟨hc ▸ holds_mem hR hp, hR⟩

open Lean Elab Tactic Meta in
/-- `wk_seg_site` (the segments of `site_cases`): a segment of the worker after its event, by
evaluation. The invariant in context gives `%p3 = false` (the thread is of warp 4 or above),
which goes in front of the start facts so that the evaluation skips the instructions it
guards, and the range of the thread index. -/
elab "wk_seg_site" : tactic => withMainContext do
  let mut hi? := none
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars ld.type)
    if ty.isAppOfArity ``Inv 3 then
      hi? := some (← Term.exprToSyntax ld.toExpr, ← Term.exprToSyntax (ty.getArg! 0),
        ← Term.exprToSyntax (ty.getArg! 1))
  let some (hi, tL, tg) := hi? | throwError "wk_seg_site: no invariant"
  let hp := mkIdent `hp3w
  Term.withoutErrToSorry <| evalTactic (← `(tactic| (
    have $hp:ident := p3_false ($hi).warp
    have := ($hi).tid
    have : 4 ≤ $tg % ($tL).block / 32 := ($hi).warp
    try (refine seg_p3 (by fact_mem) $hp:ident ?_)
    intro t h
    wk_seg h [roleAddr, warpOf, b32, $hp:ident])))

/-! ### The warp index and the branch to the worker path -/

/-- The shuffle of the warp index: lane 0's operand is the warp index, and the local code after
it (`setp.lt.u32 %p4, %r4, 4`, `@!%p4 bra`, `shl.b32 %r5, %r71, 7`, `bra.uni`) goes to the
loop's head. -/
theorem step_shfl (hs : d.site = .shfl) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, P⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim]
  have htid := hi.tid
  have hw4 : 4 ≤ g % L.block / 32 := hi.warp
  have hw8 : g % L.block / 32 < 8 := by omega
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g)
    · obtain ⟨rfl, rfl⟩ := hv
      have h1 : At (PTX.next (setReg t 465 (Value.bits 32 (BitVec.ofNat 64 (warpOf L g))))) 18
          ((465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) :: facts L g ⟨.shfl, P⟩) :=
        At.set h (facts_ne (by live_dec))
      have hp4 : (4, Value.pred false) ∈
          (4, Value.pred false) :: (465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) ::
            facts L g ⟨.shfl, P⟩ := List.mem_cons_self
      have hA : Seg kernel asms L g 1 18
          ((465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) :: facts L g ⟨.shfl, P⟩) 19
          ((4, Value.pred false) :: (465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) ::
            facts L g ⟨.shfl, P⟩) := fun t h => by
        wk_seg h [warpOf, b32]
      have hB := Seg.bra_neg (K := kernel) (A := asms) (L := L) (g := g) (pick := false)
        Flow.code_19 hp4 (fun _ _ => asms_localRule_bra) (asms_segFreePc (by decide))
      have hC : Seg kernel asms L g 2 2331
          ((4, Value.pred false) :: (465, Value.bits 32 (BitVec.ofNat 64 (warpOf L g))) ::
            facts L g ⟨.shfl, P⟩) 2337 (facts L g ⟨.loop, P⟩) := fun t h => by
        wk_seg h [warpOf, b32]
      exact step_of_seg (d' := ⟨.loop, P⟩) (by simp [next]) (hi.at) h1
        ⟨1 + (1 + 2), Seg.comp hA (Seg.comp hB hC)⟩
    · exact .inl (.inl (by simp [next, hv]))
  all_goals exact .inl (.inl (by simp [next]))

/-! ### The role byte -/

/-- No assumption of the kernel has a local rule for `brx.idx`. -/
theorem asms_localRule_brx {t : TState} {r : Nat} {targets : List Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.brx (.reg r) targets uni) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

/-- The zero-extension of a loaded value is one 32-bit word. -/
theorem extend_zero_bits {v w : Value} (h : extendLoaded (MemExt.zero 32) 8 v = .ok w) :
    ∃ y, w = .bits 32 y := by
  unfold extendLoaded at h
  cases hb : v.bitPattern with
  | none => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
  | some n =>
    simp only [hb, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨_, h.symm⟩

/-- After a one-register load with an extension whose bytes rebuild to `v`, extended to `w`. -/
theorem at_afterAccessLoad {t : TState} {F : List (Nat × Value)} {pc d : Nat} {v w : Value}
    {bs : List (Option Byte)} {ext : MemExt} {wd : Nat} (h : At t pc F)
    (hv : rebuild 3 bs = .ok v) (hx : extendLoaded ext wd v = .ok w)
    (hd : ∀ p ∈ F, p.1 ≠ d) : At (afterAccessLoad t ext wd [d] bs) (pc + 1) ((d, w) :: F) := by
  have e : afterAccessLoad t ext wd [d] bs =
      { setReg t d w with pc := t.pc + 1, sub := 0, acc := [] } := by
    simp [afterAccessLoad, hv, hx, bind, Except.bind, h.2.1, h.2.2.1, setRegs]
  rw [e]
  exact ⟨by simp [h.1], rfl, rfl, h.2.2.2.1, Function.update_self .., holds_update h.2.2.2.2 hd⟩

/-- After the load of the role byte, the local code (`setp.gt.u32 %p5, %r74, 3`, `@%p5 bra`,
`brx.idx`) goes to the role's entry. The code reads the low 32 bits of the register. -/
theorem seg_dispatch {P : Pro} {y : BitVec 64} {s : Site} (hk : (truncBits 32 y).toNat < 4)
    (hs : roleSite (truncBits 32 y).toNat = some s) :
    Seg kernel asms L g (1 + (1 + 1)) 2341
      ((535, Value.bits 32 y) :: factsAt L g 2340 ⟨.ldRole, P⟩) s.pc
      (facts L g ⟨s, P⟩) := by
  obtain ⟨k, hkk⟩ : ∃ k, (truncBits 32 y).toNat = k := ⟨_, rfl⟩
  rw [hkk] at hk hs
  have ht : [2344, 2422, 2333, 2853][k]? = some s.pc := by
    interval_cases k <;> simp only [roleSite, Option.some.injEq] at hs <;> subst hs <;> rfl
  have hmem : (535, Value.bits 32 y) ∈
      (5, Value.pred false) :: (535, Value.bits 32 y) ::
        factsAt L g 2340 ⟨.ldRole, P⟩ := by simp
  have hl : ∀ r ∈ Flow.live s.pc, r ∈ Flow.live 2340 := by
    interval_cases k <;> simp only [roleSite, Option.some.injEq] at hs <;> subst hs <;>
      live_dec
  exact Seg.comp (G := (5, Value.pred false) ::
      (535, Value.bits 32 y) :: factsAt L g 2340 ⟨.ldRole, P⟩)
    (fun t h => by wk_seg h [hkk])
    (Seg.comp (Seg.bra (pick := false) Flow.code_2342 List.mem_cons_self
      (fun _ _ => asms_localRule_bra) (asms_segFreePc (by decide)))
      (Seg.weaken_end (Seg.brx (k := k) (target := s.pc) Flow.code_2343 hmem hkk ht
        (fun _ _ => asms_localRule_brx) (asms_segFreePc (by decide)))
        fun _ hR => holds_relive (d := ⟨.ldRole, P⟩) hR.2.2 rfl hl))

/-- After the load of a role byte above 3, the local code (`setp.gt.u32 %p5, %r74, 3`, `@%p5
bra`) branches to the first barrier of the branch's block. -/
theorem seg_bad {P : Pro} {y : BitVec 64} (hk : ¬ (truncBits 32 y).toNat < 4) :
    Seg kernel asms L g (1 + 1) 2341
      ((535, Value.bits 32 y) :: factsAt L g 2340 ⟨.ldRole, P⟩) Site.bad0.pc
      (facts L g ⟨.bad0, P⟩) := by
  have hl : ∀ r ∈ Flow.live Site.bad0.pc, r ∈ Flow.live 2340 := by live_dec
  exact Seg.comp (G := (5, Value.pred true) ::
      (535, Value.bits 32 y) :: factsAt L g 2340 ⟨.ldRole, P⟩)
    (fun t h => by
      seg_fp h using
        (simp only [Value.pred.injEq]
         nf_simp [PTX.compare, decide_eq_decide, ne_eq, decide_eq_false_iff_not,
           decide_eq_true_eq]
         omega))
    (Seg.weaken_end (Seg.bra (pick := true) Flow.code_2342 List.mem_cons_self
      (fun _ _ => asms_localRule_bra) (asms_segFreePc (by decide)))
      fun _ hR => holds_relive (d := ⟨.ldRole, P⟩) hR.2.2 rfl hl)

theorem step_ldRole (hs : d.site = .ldRole) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, P⟩ := d
  simp only at hs
  subst hs
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ : ∃ a : MemAccess,
      kernel.code[2340]? = some ⟨none, .mem a⟩ ∧ a.kind = .load ∧ a.nc = false ∧
      a.locSpace? = none ∧ a.regs = [535] ∧ a.ext = .zero 32 ∧ a.elem.width = 8 :=
    ⟨_, Flow.code_2340, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load_ext ha2 ha3 ha4 hf
  rw [ha6, ha7, ha5]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, dispatch, hv],
      Machine.dead_of_fault (f := f) (by simp [afterAccessLoad, hv, bind, Except.bind])⟩
  | ok v =>
    cases hx : extendLoaded (MemExt.zero 32) 8 v with
    | error f =>
      exact .inr ⟨by simp [next, dispatch, hv, hx],
        Machine.dead_of_fault (f := f) (by simp [afterAccessLoad, hv, hx, bind, Except.bind])⟩
    | ok w =>
      obtain ⟨y, rfl⟩ := extend_zero_bits hx
      have h1 := at_afterAccessLoad (d := 535) h hv hx (facts_ne (by live_dec))
      by_cases hlt : (truncBits 32 y).toNat < 4
      · obtain ⟨s', hs'⟩ : ∃ s', roleSite (truncBits 32 y).toNat = some s' := by
          obtain ⟨k, hk⟩ : ∃ k, (truncBits 32 y).toNat = k := ⟨_, rfl⟩
          rw [hk] at hlt ⊢
          interval_cases k <;> simp [roleSite]
        exact step_of_seg (d' := ⟨s', P⟩) (by simp [next, dispatch, hv, hx, hs']) hi.at h1
          ⟨_, seg_dispatch hlt hs'⟩
      · have hn : roleSite (truncBits 32 y).toNat = none := by
          obtain ⟨k, hk⟩ : ∃ k, (truncBits 32 y).toNat = k := ⟨_, rfl⟩
          rw [hk] at hlt ⊢
          match k, hlt with
          | k + 4, _ => rfl
        exact step_of_seg (d' := ⟨.bad0, P⟩) (by simp [next, dispatch, hv, hx, hn]) hi.at h1
          ⟨_, seg_bad hlt⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Worker
