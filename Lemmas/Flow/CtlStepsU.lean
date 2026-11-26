-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LoadFrameU
public import Lemmas.Flow.LandsU
public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # One-step lemmas for UB-tolerant control machines

Kernel-independent helpers for `Code.StepAtU` obligations of a control machine whose facts are
built by `factsFrom`: the fact list's registers (`factsFrom_keys`), a fact of it
(`mem_factsFrom_eq`), naming a fact before a branch (`SegU.pick`), and one-step lemmas for a
Tensor Memory load (`Code.tcLoadU`), an element of a vector load or store (`Code.ldvU`,
`Code.vstU`), a `vote.any` (`Code.voteAnyU`) and the plain Tensor Memory fences
(`Code.fires_tcPlain_next`). -/

namespace PTX.Flow
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The registers a fact list built by `factsFrom` names. -/
theorem factsFrom_keys {v : Nat → Value} {rs : List Nat} :
    (factsFrom rs v).map Prod.fst = rs := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

/-- A fact of a `factsFrom` list. -/
theorem mem_factsFrom_eq {rs : List Nat} {v : Nat → Value} {r : Nat} {x : Value} (hr : r ∈ rs)
    (hv : v r = x) : (r, x) ∈ factsFrom rs v :=
  hv ▸ List.mem_map_of_mem hr

/-- A segment may start by naming one of its facts first (to branch on it). -/
theorem SegU.pick {a b : Nat} {F G : List (Nat × Value)} {r : Nat} {x : Value} (hm : (r, x) ∈ F)
    (h : SegU K A L g a ((r, x) :: F) b G) :
    SegU K A L g a F b G := fun t ⟨hP, hS0, hA, hFl, hR⟩ =>
  h t ⟨hP, hS0, hA, hFl, holds_mem hR hm, hR⟩

end PTX.Flow

namespace PTX.Flow.Code
open PTX.Proof PTX.EventFrame

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A Tensor Memory load without implicit wait whose destinations the facts do not name. -/
theorem tcLoadU {d dn : C.D} {ds : List Nat} {ta : Nat} {sh : TcShape} {live : List Nat}
    {val : Nat → Value}
    (hc : K.code[C.pc d]? = some ⟨none, .tcLd ds ta sh⟩) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait (C.pc d)) = false) (hF : C.facts d = factsFrom live val)
    (hoff : live.all (fun r => !ds.contains r && live.contains r) = true)
    (hn : ∀ a vals, C.next d ⟨C.pc d, .tc (.ld a vals sh)⟩ = some (some dn))
    (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (seg : SegU K A L g (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) : C.StepAtU d where
  site := fun _ => ⟨_, hc, rfl, trivial⟩
  step := by
    intro t e u ins h _ hins hf
    obtain rfl := Option.some.inj (hins.symm.trans hc)
    have ht := at_of_atD h hs hacc
    obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
    obtain ⟨a, vals, -, rfl, rfl⟩ := fires_tcLd hsh hf (by rw [hP]; exact hw)
    obtain ⟨hp, hsb, hac, hfl⟩ := setRegs_skel (PTX.next t) ds vals
    have hreg := hR
    rw [hF] at hreg
    obtain ⟨u, hl, hu⟩ := landsU (u := setRegs (PTX.next t) ds vals)
      ⟨hp.trans (congrArg (· + 1) hP), hsb.trans hS0, hac.trans hA,
        hfl.trans hFl, hF ▸ holds_after_tcLd hreg hoff⟩ seg hi hs' hacc'
    exact .inl (.inr ⟨dn, u, hn _ _, hl, hu⟩)

/-- An element of a vector load into registers the facts do not name: before the last element
the machine accumulates the value at the same instruction; at the last it continues by a
segment. A payload that does not rebuild faults (the machine goes on to `dbad`). -/
theorem ldvU {d : C.D} {dok : Value → C.D} {dbad : C.D} {a : MemAccess} {live : List Nat}
    {val : Nat → Value}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dok v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = some (some dbad))
    (mid : C.sub d + 1 < a.regs.length → ∀ v, C.pc (dok v) = C.pc d ∧
      C.sub (dok v) = C.sub d + 1 ∧ C.acc (dok v) = C.acc d ++ [v] ∧
      C.facts (dok v) = C.facts d ∧ C.inv (dok v))
    (hF : C.facts d = factsFrom live val) (hoff : ∀ r ∈ live, r ∉ a.regs)
    (last : ¬ C.sub d + 1 < a.regs.length → ∀ v, C.sub (dok v) = 0 ∧ C.acc (dok v) = [] ∧
      C.inv (dok v) ∧ SegU K A L g (C.pc d + 1) (C.facts d) (C.pc (dok v)) (C.facts (dok v))) :
    C.StepAtU d where
  site := fun _ => ⟨_, hc0, hl, trivial⟩
  step := by
    intro t e u ins h hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans hc0)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
    obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
    cases hv : rebuild 3 bs with
    | error f =>
      obtain ⟨s, hs1, hs2⟩ := goodU_of_dead dbad
        (Machine.dead_of_fault (K := K) (A := A) (L := L) (g := g) (f := f)
          (u := afterLoad t a.regs bs)
          (by simp [afterLoad, hv]))
      exact .inl (.inr ⟨dbad, s, herr x bs f hv, hs1, hs2⟩)
    | ok v =>
      by_cases hm : C.sub d + 1 < a.regs.length
      · obtain ⟨hpc, hs, ha, hF', hinv⟩ := mid hm v
        have hm' : t.sub + 1 < a.regs.length := by rw [hS0]; exact hm
        have hu : afterLoad t a.regs bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
          simp [afterLoad, hv, hm']
        rw [hu]
        refine .inl (.inr ⟨dok v, _, hok x bs v hv, .refl,
          .inl ⟨⟨?_, ?_, ?_, hFl, ?_⟩, hinv⟩⟩)
        · exact hP.trans hpc.symm
        · show t.sub + 1 = C.sub (dok v)
          rw [hS0, hs]
        · show t.acc ++ [v] = C.acc (dok v)
          rw [hA, ha]
        · rw [hF']; exact hR
      · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm v
        have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hS0]; exact hm
        have hu : afterLoad t a.regs bs =
            { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
          simp [afterLoad, hv, hm']
        rw [hu]
        obtain ⟨-, -, -, hskF⟩ := setRegs_skel t a.regs (t.acc ++ [v])
        have hreg := hR
        rw [hF] at hreg
        obtain ⟨s, hl', hs'⟩ := landsU
          (u := { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] })
          ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl,
            by show (setRegs t a.regs (t.acc ++ [v])).fault = none; rw [hskF]; exact hFl,
            by rw [hF]; exact holds_setRegs_frame hreg (fun r hr => ⟨hoff r hr, hr, rfl⟩)⟩
          seg hinv hs0 ha0
        exact .inl (.inr ⟨dok v, s, hok x bs v hv, hl', hs'⟩)

/-- A successful `vote.any` records the lanes' reduction in its predicate destination. -/
theorem fires_voteAnyU {t u : TState} {pc dv pr : Nat} {neg : Bool} {ty : Option DType}
    {mask : Opnd} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.vote .any neg, ty, [some dv], [.reg pr],
      some mask⟩)) e (some u)) :
    ∃ m p r, e = ⟨pc, .voteMode .any m p r⟩ ∧ u = PTX.next (setReg t dv (.pred r)) := by
  have hw : warpTmpl L g t ⟨.vote .any neg, ty, [some dv], [.reg pr], some mask⟩ =
      voteModeTmpl L g t .any dv pr neg mask := rfl
  simp only [eventTmpl, hw, voteModeTmpl] at hf
  cases hm : readBits L g t 32 mask with
  | error f => simp only [hm, Fires] at hf; cases hf.2
  | ok m =>
    cases hp : readPred L g t (.reg pr) with
    | error f => simp only [hm, hp, Fires] at hf; cases hf.2
    | ok pred =>
      simp only [hm, hp] at hf
      split at hf
      · split at hf
        · obtain ⟨r, he, hu⟩ := hf
          exact ⟨_, _, r, he, Option.some.inj hu⟩
        · cases hf.2
      · cases hf.2

/-- A `vote.any` whose result decides the successor. -/
theorem voteAnyU {d : C.D} {dst : Bool → C.D} {ty dv pr neg mask}
    (hc : K.code[C.pc d]? = some ⟨none, .warp ⟨.vote .any neg, ty, [some dv], [.reg pr],
      some mask⟩⟩)
    (hoff : dv ∉ (C.facts d).map Prod.fst)
    (hn : ∀ m p r, C.next d ⟨C.pc d, .voteMode .any m p r⟩ = some (some (dst r)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ r, C.sub (dst r) = 0)
    (ha' : ∀ r, C.acc (dst r) = []) (hi : ∀ r, C.inv (dst r))
    (seg : ∀ r, SegU K A L g (C.pc d + 1) ((dv, .pred r) :: C.facts d) (C.pc (dst r))
      (C.facts (dst r))) : C.StepAtU d where
  site := fun _ => ⟨_, hc, rfl, trivial⟩
  step := by
    intro t e u ins hat _ hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨m, p, r, rfl, rfl⟩ := fires_voteAnyU hf
    have ht := At.set (r := dv) (v := .pred r) (at_of_atD hat hs ha)
      (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))
    obtain ⟨u, ht, hu⟩ := landsU ht (seg r) (hi r) (hs' r) (ha' r)
    exact .inl (.inr ⟨dst r, u, hn m p r, ht, hu⟩)

/-- An element of a vector store: before the last element the machine counts it at the same
instruction; at the last it continues by a segment. -/
theorem vstU {d dn : C.D} {a : MemAccess}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hst : a.kind = .store) (hn : ∀ e, C.next d e = some (some dn)) (hacc : C.acc d = [])
    (mid : C.sub d + 1 < a.srcs.length → C.pc dn = C.pc d ∧ C.sub dn = C.sub d + 1 ∧
      C.acc dn = [] ∧ C.facts dn = C.facts d ∧ C.inv dn)
    (last : ¬ C.sub d + 1 < a.srcs.length → C.sub dn = 0 ∧ C.acc dn = [] ∧ C.inv dn ∧
      SegU K A L g (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) : C.StepAtU d where
  site := fun _ => ⟨_, hc, hl, trivial⟩
  step := by
    intro t e u ins h _ hins hf
    obtain rfl := Option.some.inj (hins.symm.trans hc)
    obtain ⟨_, _, rfl, rfl⟩ := fires_st hst hf
    obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
    by_cases hm : C.sub d + 1 < a.srcs.length
    · obtain ⟨hpc, hs, ha, hF, hinv⟩ := mid hm
      rw [afterStore_mid (by rw [hS0]; exact hm)]
      refine .inl (.inr ⟨dn, _, hn _, .refl, .inl ⟨⟨hP.trans hpc.symm, ?_,
        hA.trans (hacc.trans ha.symm), hFl, hF ▸ hR⟩, hinv⟩⟩)
      show t.sub + 1 = C.sub dn
      rw [hS0, hs]
    · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm
      rw [afterStore_last (by rw [hS0]; exact hm)]
      obtain ⟨u, ht, hu⟩ := landsU (u := { t with pc := t.pc + 1, sub := 0 })
        ⟨congrArg (· + 1) hP, rfl, hA.trans hacc, hFl, hR⟩ seg hinv hs0 ha0
      exact .inl (.inr ⟨dn, u, hn _, ht, hu⟩)

/-- The Tensor Memory fences and the load wait continue at the next instruction. -/
theorem fires_tcPlain_next {op : Op}
    (hop : op = .tcFenceAfter ∨ op = .tcFenceBefore ∨ op = .tcWaitLd)
    {t u : TState} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t op) e (some u)) : u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t) (eventTmpl A L g t op) := by
    rcases hop with rfl | rfl | rfl
    all_goals simp only [eventTmpl, tcTmpl]
    all_goals try apply ofExec_frame
    all_goals repeat' first
      | rfl
      | exact True.intro
      | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

end PTX.Flow.Code
