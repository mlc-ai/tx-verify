-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQCtl
public import Lemmas.Flow.SegQF
public import Lemmas.Flow.RunFrame
public meta import Lean

@[expose] public section

/-! # Control segments under the float tag invariant (`segqf_ctlv`)

The twin of `segq_ctlv` (`Lemmas/Flow/SegQCtlV.lean`) for `QTF qt`: the plain-stretch hypotheses
`PlainRules` become the soundness `AbsSound` of the abstract rule over a range containing the
stretch. The exact pieces are strict segments that also pass the typed check
(`segQF_of_seg_typed`) or keep the tagged registers (`SegQF.of_seg_frame`), the others are typed
pieces (`segQF_of_typed`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
  {abs : EnvF → Op → Option (List (Nat × TagF))}

theorem AbsSound.mono {a b a' b' : Nat} (h : AbsSound A L g a b abs) (h1 : a ≤ a')
    (h2 : b' ≤ b) : AbsSound A L g a' b' abs :=
  fun env op outs t ho ha hb => h env op outs t ho (by omega) (by omega)

/-- **An exact piece under the float tag invariant**: a strict segment (`Seg`) whose stretch also
passes the typed check. -/
theorem segQF_of_seg_typed (qt : Nat → EnvF) {Ft : Env} {a b n : Nat} {F G : List (Nat × Value)}
    (hseg : Seg K A L g n a F b G) (hn : n = b - a) (hab : a ≤ b) (hlen : b ≤ K.code.length)
    (hA : AbsSound A L g a b abs) (hF : FactTags F Ft)
    (hc : checkF abs qt a b Ft [] ((K.code.drop a).take (b - a)) = true) :
    SegQ K A L g (QTF qt) a F b G := by
  intro t ht hq
  obtain ⟨u, hu, -, hQ, -⟩ := typedF_run (K := K) (abs := abs) qt hab hlen hA hF hc ht hq
  obtain ⟨u2, hu2, hAt⟩ := hseg t ht
  subst hn
  rw [hu] at hu2
  obtain rfl := Option.some.inj hu2
  exact ⟨u, run_rtg hu, hAt, hQ⟩

/-- **An exact piece that keeps the tagged registers** (the twin of `SegQ.of_seg_frame`). -/
theorem SegQF.of_seg_frame {qt : Nat → EnvF} {a b n : Nat} {F G : List (Nat × Value)}
    (hA : RulesFrame A) (hseg : Seg K A L g n a F b G) (hn : n = b - a)
    (hlen : b ≤ K.code.length) (hab : a ≤ b) (hS : PlainSegs A a b)
    (hB : frameB ((K.code.drop a).take n) ((qt b).map Prod.fst) = true)
    (hq : tagsInF (qt b) (qt a) = true) : SegQ K A L g (QTF qt) a F b G := by
  intro t ht hQ
  obtain ⟨u, hu, hAt⟩ := hseg t ht
  have hlen' : ((K.code.drop a).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  have hfr := run_frame hA n a _ t u rfl hlen' hB (fun i hi => hS (a + i) (by omega) (by omega))
    ht.1 ht.2.2.2.1 hu
  refine ⟨u, run_rtg hu, hAt, ?_⟩
  have hT := typedF_of_tagsIn hq (by simpa [QTF, ht.1] using hQ : TypedF (qt a) t)
  intro r tg hr
  rw [hAt.1] at hr
  rw [hfr r (List.mem_map_of_mem (f := Prod.fst) (lookup_mem' hr))]
  exact hT r tg hr

end PTX.Flow.TyG

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow.Tagged PTX.Flow.Havoc Lean Meta Elab Tactic

/-- `segq_ctlv` for `QTF qt`: `hAbs` is `AbsSound` and `hS` `PlainSegs` over a range containing
the stretch, `hA` the rules' frame. -/
syntax "segqf_ctlv " term:max ", " term:max ", " term:max ", " term:max " using " tacticSeq :
  tactic

/-- `segqf_ctlv` whose cuts take the register values of the target's table. -/
syntax "segqf_ctlt " term:max ", " term:max ", " term:max ", " term:max " using " tacticSeq :
  tactic

meta def runSegqF (qt hN hS hA : TSyntax `term) (vals : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (tbl : Bool) : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``SegQ 9 do throwError "segqf_ctl: expected SegQ"
  let #[k, asms, launch, thread, _q, a, f, b, g] := target.getAppArgs |
    throwError "segqf_ctl: expected SegQ"
  let pair ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Value]
  let finish ← factValuesQ g
  let start ← natValue a
  let stop ← natValue b
  unless start ≤ stop do throwError "segqf_ctl: backward stretch"
  let pieces ← sliceQ (← mkAppM ``Kernel.code #[k]) start stop finish.toArray.unzip.1
  let mut input := f
  let mut todo := pieces
  if todo.isEmpty then todo := [⟨start, stop, false, #[]⟩]
  for p in todo do
    let last := p.hi == stop
    let known ← factValuesQ input
    let output ← if last then pure g else do
      let mut entries := #[]
      for r in p.live do
        let v ← if tbl && p.exactStep then do
            match finish[r]? with
            | some v => pure v
            | none =>
              match (← splitFacts g).2 with
              | some (_, f) => pure (mkApp f (mkNatLit r))
              | none => throwError "segqf_ctlt: no table value for register {r}"
          else if p.exactStep then do
          let o ← whnfD (← mkAppM ``PTX.Flow.checkpoint #[k, asms, launch, thread, mkNatLit p.lo,
            mkNatLit (p.hi - p.lo), input, mkNatLit r])
          unless o.isAppOfArity ``Option.some 2 do
            throwError "segqf_ctl: cannot compute register {r} at checkpoint {p.hi}"
          pure (o.getArg! 1)
          else match known[r]? with
            | some v => pure v
            | none => throwError "segqf_ctl: missing input for register {r} at {p.lo}"
        entries := entries.push (← mkAppM ``Prod.mk #[mkNatLit r, v])
      mkListLit pair entries.toList
    unless last do
      let mid ← Term.exprToSyntax output
      let pc := quote p.hi
      evalTactic (← `(tactic| refine SegQ.comp (b := $pc) (G := $mid) ?_ ?_))
    let regs ← pieceRegs k (← mkAppM ``Kernel.code #[k]) p.lo p.hi
    let ft ← Term.exprToSyntax (← factTagList known regs)
    if p.exactStep then
      let n := quote (p.hi - p.lo)
      evalTactic (← `(tactic| focus
        first
        | refine segQF_of_seg_typed $qt (Ft := $ft) (n := $n) ?_ rfl (by decide +kernel)
            (by decide +kernel) (AbsSound.mono $hN (by decide +kernel) (by decide +kernel))
            (factTags_of_B (by rfl)) (by decide +kernel)
        | refine SegQF.of_seg_frame $hA ?_ rfl (by decide +kernel) (by decide +kernel)
            (PlainSegs.mono $hS (by decide +kernel) (by decide +kernel))
            (by decide +kernel) (by decide +kernel)
        intro t ht
        seg_fp ht using $vals))
    else
      let keys ← Term.exprToSyntax (← mkRegList (← regList
        (← mkAppM ``List.map #[← mkAppOptM ``Prod.fst #[some (mkConst ``Nat),
          some (mkConst ``Value)], output])))
      evalTactic (← `(tactic| focus
        refine segQF_of_typed $qt (Ft := $ft) (by decide +kernel) (by decide +kernel)
          (AbsSound.mono $hN (by decide +kernel) (by decide +kernel))
          (factTags_of_B (by rfl))
          (by change checkF _ _ _ _ _ $keys _ = true; decide +kernel) ?_
        apply PTX.Flow.Selected.subset
        repeat' apply And.intro (by
          first
          | rfl
          | (simp only [List.lookup, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
              beq_self_eq_true, Option.some.injEq]
             first | rfl | ($vals))
          | ($vals))
        exact True.intro))
    input ← instantiateMVars output

elab_rules : tactic
  | `(tactic| segqf_ctlv $qt, $hN, $hS, $hA using $vals) => runSegqF qt hN hS hA vals false
  | `(tactic| segqf_ctlt $qt, $hN, $hS, $hA using $vals) => runSegqF qt hN hS hA vals true

end PTX.Flow.TyG
