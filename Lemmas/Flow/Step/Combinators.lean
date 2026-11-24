-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code
public import Lemmas.Flow.Next
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Tc
public import Lemmas.Flow.TcMmaTs
public import Lemmas.Flow.Async
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Local
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.Vector

@[expose] public section

/-! # Step combinators of site machines

A proof tool. `Code.StepAt d` asks, for the abstract state `d`, that every event fired at its
site reaches a concrete state of the successor `next` gives. Each lemma below discharges that
obligation (`StepOk`) for one class of event instruction, from the inversion lemma of the class
(`fires_wait`, `fires_elect`, `fires_shfl`, `fires_load`, `fires_st`, `fires_vote`, or an
`advances` fact):

* `step_issue`: an event that continues at the next instruction whatever it observed
  (`step_arrive`: an arrival, which clears its state destination);
* `step_wait`: an mbarrier poll, which continues with its predicate set to the outcome;
* `step_elect`: an election, which sets the elected predicate (and the leader register);
* `step_shfl`: a shuffle whose machine follows one received value (`step_shfl_rec`: records it;
  `step_shfl_sel`: its successor is any function of the value received);
* `step_load`: a scalar load, whose machine records the value read (`step_load_sel`: whose
  successor is any function of the value read, including stopping on it);
* `step_vec_mid`, `step_vec_last`: an element of a vector store (or a scalar store);
* `step_stop`: an event after which the machine stops following the thread;
* `step_vote`: a ballot vote of a predicate fact, whose machine records the ballot;
* `step_exit`: `ret` or `exit`, which fires no continuing event.

Each successor is given by `Lands`: a local segment from the facts after the event to the
successor's site, the successor at sub-step 0 with an empty accumulator, and its invariant. The
lemmas name the machine only through `C.pc`, `C.facts`, `C.next`, `C.inv`, `C.sub` and `C.acc`. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- What `StepAt.step` asks after the event `e` fired at `d` and left the thread in `u`. -/
abbrev Cont (C : Code K A L g) (d : C.D) (e : Event) (u : TState) : Prop :=
  (C.next d e = some none ∨
      ∃ d' t', C.next d e = some (some d') ∧ Relation.ReflTransGen (Tau K A L g) u t' ∧
        C.Good (some d') t') ∨
    (C.next d e = none ∧ Machine.Dead (K := K) (A := A) (L := L) (g := g) u)

/-- The `step` field of `StepAt` at one abstract state. -/
structure StepOk (C : Code K A L g) (d : C.D) : Prop where
  step : ∀ {t e u} ins, C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
    Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) → C.Cont d e u

/-- `StepAt` from its two fields. -/
theorem StepAt.of {d : C.D} (hsite : C.inv d → ∃ ins, K.code[C.pc d]? = some ins ∧
    ins.op.isLocal = false ∧ GuardTrue (C.facts d) ins.guard) (hstep : C.StepOk d) :
    C.StepAt d :=
  ⟨hsite, hstep.step⟩

/-- The successor `d'` of `d` is reached from a state at `s` with facts `F`: under `d`'s
invariant, local steps lead to its site with its facts; it sits at sub-step 0 with an empty
accumulator; and `d`'s invariant gives its invariant. -/
structure Lands (C : Code K A L g) (d : C.D) (s : Nat) (F : List (Nat × Value)) (d' : C.D) :
    Prop where
  seg : C.inv d → ∃ n, Seg K A L g n s F (C.pc d') (C.facts d')
  sub : C.sub d' = 0
  acc : C.acc d' = []
  inv : C.inv d → C.inv d'

/-- The facts after an election into the predicate and, if there is one, the leader register. -/
def electFacts (dst : Option Nat) (ld : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  match dst with
  | none => F
  | some r => (r, .bits 32 (BitVec.ofNat 64 ld)) :: F

/-- A predicate guard read from a value table holds when the table gives it the guard's value. -/
theorem guardTrue_factsFrom {live : List Nat} {v : Nat → Value} {p : Nat} {neg : Bool}
    (hp : p ∈ live) (hv : v p = .pred (!neg)) : GuardTrue (factsFrom live v) (some (p, neg)) := by
  show (p, Value.pred (!neg)) ∈ factsFrom live v
  rw [← hv]
  exact mem_factsFrom hp

theorem at_of_atD {d : C.D} {t : TState} (h : C.AtD d t) (hs : C.sub d = 0)
    (ha : C.acc d = []) : At t (C.pc d) (C.facts d) :=
  ⟨h.1, h.2.1.trans hs, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩

theorem Lands.cont {d d' : C.D} {e : Event} {u : TState} {s : Nat} {F : List (Nat × Value)}
    (hl : C.Lands d s F d') (hi : C.inv d) (hn : C.next d e = some (some d')) (hu : At u s F) :
    C.Cont d e u := by
  obtain ⟨n, hseg⟩ := hl.seg hi
  obtain ⟨t', hr, ht⟩ := hseg u hu
  exact .inl (.inr ⟨d', t', hn, run_rtg hr,
    ⟨⟨ht.1, ht.2.1.trans hl.sub.symm, ht.2.2.1.trans hl.acc.symm, ht.2.2.2.1, ht.2.2.2.2⟩,
      hl.inv hi⟩⟩)

/-- An event that continues at the next instruction whatever it observed (`hadv`, e.g. an
MMA, a commit, `bar.sync`, `setmaxnreg`, an arrival without state): the local code from there
to the successor `dn`. -/
theorem step_issue {d dn : C.D} {ins0 : Instr} (hc0 : K.code[C.pc d]? = some ins0)
    (hadv : ∀ {t e u}, Fires (C.pc d) (eventTmpl A L g t ins0.op) e (some u) → u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := hadv hf
  exact hl.cont hi (hn e) (At.next (at_of_atD h hs ha))

/-- After an arrival the thread is at the next instruction with its state destination cleared. -/
theorem fires_arrive_next {t u : TState} {base : Nat} {off : Int} {tx count : Opnd}
    {cluster release : Bool} {scope : MbarScope} {state : Option Nat} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t
      (.mbarArrive base off tx count cluster release scope state)) e (some u)) :
    u = PTX.next (mbarStateDest t state) := by
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) with
  | error f =>
    cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
      simp only [Bool.false_eq_true, ↓reduceIte, hm, ofExec, widenMbarScope, ite_self,
        Fires] at hf <;> simp at hf
  | ok m =>
    cases hb : readBits L g t 32 tx with
    | error f =>
      cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
        simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, ofExec, widenMbarScope, ite_self,
          Fires] at hf <;> simp at hf
    | ok bytes =>
      cases hn : readBits L g t 32 count with
      | error f =>
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec, widenMbarScope,
            ite_self, Fires] at hf <;> simp at hf
      | ok n =>
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec] at hf <;>
          cases release <;> cases scope <;> simp only [widenMbarScope] at hf <;>
          split_ifs at hf <;> exact Option.some.inj hf.2

/-- An arrival, which continues at the next instruction with its state destination register
cleared (no fact names it). -/
theorem step_arrive {d dn : C.D} {gd : Option (Nat × Bool)} {base : Nat} {off : Int}
    {tx count : Opnd} {cluster release : Bool} {scope : MbarScope} {state : Option Nat}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mbarArrive base off tx count cluster release scope state⟩)
    (hst : ∀ r ∈ state, ∀ q ∈ C.facts d, q.1 ≠ r)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := fires_arrive_next hf
  have h0 := at_of_atD h hs ha
  refine hl.cont hi (hn e) ?_
  cases state with
  | none => exact At.next h0
  | some r =>
    exact ⟨congrArg (· + 1) h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1,
      holds_update h0.2.2.2.2 (hst r rfl)⟩

/-- An mbarrier poll into predicate `p`: the successful poll continues to `dok`, the failed one
to `dfail`. -/
theorem step_wait {d dok dfail : C.D} {gd : Option (Nat × Bool)} {p base : Nat} {off : Int}
    {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mbarWait p base off par acq sc⟩)
    (hp : ∀ q ∈ C.facts d, q.1 ≠ p)
    (hok : ∀ m q a s, C.next d ⟨C.pc d, .wait m q true a s⟩ = some (some dok))
    (hfail : ∀ m q a s, C.next d ⟨C.pc d, .wait m q false a s⟩ = some (some dfail))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hlok : C.Lands d (C.pc d + 1) ((p, .pred true) :: C.facts d) dok)
    (hlfail : C.Lands d (C.pc d + 1) ((p, .pred false) :: C.facts d) dfail) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  rw [← h.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := p) (v := .pred ok) h0 hp
  rw [h.1]
  cases ok with
  | false => exact hlfail.cont hi (hfail m q acq s) h1
  | true => exact hlok.cont hi (hok m q acq s) h1

/-- An election into predicate `p` and, if `dst` names one, the leader register: the elected
lane continues to `dl`, the others to `ds`. -/
theorem step_elect {d dl ds : C.D} {gd : Option (Nat × Bool)} {ty : Option DType}
    {dst : Option Nat} {p : Nat} {mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.elect, ty, [dst, some p], [], some mask⟩⟩)
    (hp : ∀ q ∈ C.facts d, q.1 ≠ p)
    (hd : ∀ r ∈ dst, (∀ q ∈ C.facts d, q.1 ≠ r) ∧ r ≠ p)
    (hnl : ∀ mk inst ld, laneOf L g = ld →
      C.next d ⟨C.pc d, .elect mk inst ld⟩ = some (some dl))
    (hns : ∀ mk inst ld, laneOf L g ≠ ld →
      C.next d ⟨C.pc d, .elect mk inst ld⟩ = some (some ds))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hll : ∀ ld, C.Lands d (C.pc d + 1) ((p, .pred true) :: electFacts dst ld (C.facts d)) dl)
    (hls : ∀ ld, C.Lands d (C.pc d + 1) ((p, .pred false) :: electFacts dst ld (C.facts d))
      ds) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  -- the state before the predicate is written, with the leader register set
  have h1 : ∃ t1, At t1 (C.pc d) (electFacts dst ld (C.facts d)) ∧
      (dst.elim t fun r => setReg t r (.bits 32 (BitVec.ofNat 64 ld))) = t1 := by
    cases dst with
    | none => exact ⟨t, h0, rfl⟩
    | some r =>
      obtain ⟨hr, -⟩ := hd r rfl
      exact ⟨setReg t r (.bits 32 (BitVec.ofNat 64 ld)), ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1,
        Function.update_self .., holds_update h0.2.2.2.2 hr⟩, rfl⟩
  obtain ⟨t1, ht1, he⟩ := h1
  rw [he]
  have hp' : ∀ q ∈ electFacts dst ld (C.facts d), q.1 ≠ p := by
    cases dst with
    | none => exact hp
    | some r =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (hd r rfl).2
      · exact hp q hq
  by_cases hld : laneOf L g = ld
  · have hb : (laneOf L g == ld) = true := by simp [hld]
    rw [hb]
    exact (hll ld).cont hi (hnl mk inst ld hld) (At.set ht1 hp')
  · have hb : (laneOf L g == ld) = false := by simp [hld]
    rw [hb]
    exact (hls ld).cont hi (hns mk inst ld hld) (At.set ht1 hp')

/-- A shuffle into register `r` whose machine follows the received value `v` only: another
value stops the machine (`some none`), `v` continues to `dok`. -/
theorem step_shfl {d dok : C.D} {gd : Option (Nat × Bool)} {mode : ShflMode}
    {ty : Option DType} {r : Nat} {a b c mask : Opnd} {v : Value}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.shfl mode, ty, [some r], [a, b, c], some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ =
      if recv = v then some (some dok) else some none)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : C.Lands d (C.pc d + 1) ((r, v) :: C.facts d) dok) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  by_cases hv : recv = v
  · subst hv
    exact hl.cont hi (by rw [hn]; simp) (At.set (at_of_atD h hs ha) hr)
  · exact .inl (.inl (by rw [hn]; simp [hv]))

/-- A shuffle into register `r` whose machine records the received value. -/
theorem step_shfl_rec {d : C.D} {dok : Value → C.D} {gd : Option (Nat × Bool)}
    {mode : ShflMode} {ty : Option DType} {r : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.shfl mode, ty, [some r], [a, b, c], some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ =
      some (some (dok recv)))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ v, C.Lands d (C.pc d + 1) ((r, v) :: C.facts d) (dok v)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  exact (hl recv).cont hi (hn ..) (At.set (at_of_atD h hs ha) hr)

/-- A shuffle into register `r` whose machine's successor is a function `nv` of the received value:
it may follow the value to a state or stop following on it (`some none`). -/
theorem step_shfl_sel {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {mode : ShflMode} {ty : Option DType} {r : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.shfl mode, ty, [some r], [a, b, c], some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = nv recv)
    (hs : C.sub d = 0) (ha : C.acc d = []) (hnn : ∀ v, nv v ≠ none)
    (hl : ∀ v d', nv v = some (some d') → C.Lands d (C.pc d + 1) ((r, v) :: C.facts d) d') :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  have hnr := hn mode av bv cv recv ok
  rcases hv : nv recv with _ | _ | d'
  · exact absurd hv (hnn recv)
  · exact .inl (.inl (hnr.trans hv))
  · exact (hl recv d' hv).cont hi (hnr.trans hv) (At.set (at_of_atD h hs ha) hr)

/-- A shuffle into register `r` whose machine's successor is a function `nv` of the received value,
where the value may also kill the thread (`nv v = none`): the local code after it reaches undefined
behaviour (a division without a rule, say). -/
theorem step_shfl_dead {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {mode : ShflMode} {ty : Option DType} {r : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.shfl mode, ty, [some r], [a, b, c], some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = nv recv)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ v d', nv v = some (some d') → C.Lands d (C.pc d + 1) ((r, v) :: C.facts d) d')
    (hdead : ∀ v, nv v = none → C.inv d →
      ∀ u, At u (C.pc d + 1) ((r, v) :: C.facts d) →
        Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  have hnr := hn mode av bv cv recv ok
  have hat := At.set (v := recv) (at_of_atD h hs ha) hr
  rcases hv : nv recv with _ | _ | d'
  · exact .inr ⟨hnr.trans hv, hdead recv hv hi _ hat⟩
  · exact .inl (.inl (hnr.trans hv))
  · exact (hl recv d' hv).cont hi (hnr.trans hv) hat

/-- A scalar load into register `r` whose machine records the value read; bytes that do not
rebuild a value fault the thread, where the machine stops (`next = none`). -/
theorem step_load {d : C.D} {dok : Value → C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    {r : Nat} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hregs : a.regs = [r])
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dok v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ v, C.Lands d (C.pc d + 1) ((r, v) :: C.facts d) (dok v)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨herr x bs f hv, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    have hst : { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } =
        PTX.next (setReg t r v) := by
      have hs0 := h0.2.1
      have ha0 := h0.2.2.1
      cases t
      simp_all [PTX.next, setReg]
    rw [afterLoad_ok h0.2.1 h0.2.2.1 hv, hst]
    exact (hl v).cont hi (hok x bs v hv) (At.set h0 hr)

/-- The facts other than those of register `r`. -/
def dropReg (r : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  F.filter fun q => q.1 != r

theorem dropReg_factsFrom (r : Nat) (live : List Nat) (val : Nat → Value) :
    dropReg r (factsFrom live val) = factsFrom (live.filter fun x => x != r) val := by
  simp only [dropReg, factsFrom, List.filter_map]
  rfl

theorem holds_dropReg {R : Nat → Option Value} {F : List (Nat × Value)} (r : Nat)
    (h : Holds R F) : Holds R (dropReg r F) := by
  induction F with
  | nil => trivial
  | cons p F ih =>
    obtain ⟨q, v⟩ := p
    simp only [dropReg, List.filter_cons] at ih ⊢
    split
    · exact ⟨h.1, ih h.2⟩
    · exact ih h.2

/-- A scalar load into register `r` whose machine's successor is a function `nv` of the value
read: it may follow the value to a state (`some (some d')`) or stop on it (`some none`), but it
does not fault on a value that rebuilds (`nv v ≠ none`). Bytes that do not rebuild fault the
thread, where the machine stops (`none`) or stops following it (`some none`). The register may
hold a fact before the load (a guarded load's default): the facts after it are the value read
and the other facts (`dropReg`). -/
theorem step_load_sel {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} {r : Nat} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same) (hregs : a.regs = [r])
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hs : C.sub d = 0) (ha : C.acc d = []) (hnn : ∀ v, nv v ≠ none)
    (hl : ∀ v d', nv v = some (some d') →
      C.Lands d (C.pc d + 1) ((r, v) :: dropReg r (C.facts d)) d') :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hst : { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } =
        PTX.next (setReg t r v) := by
      have hs0 := h0.2.1
      have ha0 := h0.2.2.1
      cases t
      simp_all [PTX.next, setReg]
    rw [afterLoad_ok h0.2.1 h0.2.2.1 hv, hst]
    have h1 : At t (C.pc d) (dropReg r (C.facts d)) := h0.mono (holds_dropReg r h0.2.2.2.2)
    have hr : ∀ q ∈ dropReg r (C.facts d), q.1 ≠ r := fun q hq => by
      simpa using (List.mem_filter.mp hq).2
    have hn := hok x bs v hv
    rcases hnv : nv v with _ | _ | d'
    · exact absurd hnv (hnn v)
    · exact .inl (.inl (hn.trans hnv))
    · exact (hl v d' hnv).cont hi (hn.trans hnv) (At.set h1 hr)

/-- A scalar load (not `.nc`, no extension) whose successor is a function `nv` of the value
read, where `nv v = none` means the thread dies by its local steps after the load (a `trap`
the code reaches on that value, M1), as `step_shfl_dead` for a shuffle. -/
theorem step_load_dead {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} {r : Nat} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same) (hregs : a.regs = [r])
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ v d', nv v = some (some d') →
      C.Lands d (C.pc d + 1) ((r, v) :: dropReg r (C.facts d)) d')
    (hdead : ∀ v, nv v = none → C.inv d →
      ∀ u, At u (C.pc d + 1) ((r, v) :: dropReg r (C.facts d)) →
        Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hst : { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } =
        PTX.next (setReg t r v) := by
      have hs0 := h0.2.1
      have ha0 := h0.2.2.1
      cases t
      simp_all [PTX.next, setReg]
    rw [afterLoad_ok h0.2.1 h0.2.2.1 hv, hst]
    have h1 : At t (C.pc d) (dropReg r (C.facts d)) := h0.mono (holds_dropReg r h0.2.2.2.2)
    have hr : ∀ q ∈ dropReg r (C.facts d), q.1 ≠ r := fun q hq => by
      simpa using (List.mem_filter.mp hq).2
    have hn := hok x bs v hv
    have hat := At.set (v := v) h1 hr
    rcases hnv : nv v with _ | _ | d'
    · exact .inr ⟨hn.trans hnv, hdead v hnv hi _ hat⟩
    · exact .inl (.inl (hn.trans hnv))
    · exact (hl v d' hnv).cont hi (hn.trans hnv) hat

/-- An event after which the machine stops following the thread whatever it observed (the end
of a role, whose next instruction another machine follows). -/
theorem step_stop {d : C.D} (hn : ∀ e, C.next d e = some none) : C.StepOk d :=
  ⟨fun _ _ _ _ _ => .inl (.inl (hn _))⟩

/-- An element of a vector store other than the last: the thread stays at the instruction with
the next element (`C.sub dn = C.sub d + 1`), with the same facts. -/
theorem step_vec_mid {d dn : C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .store)
    (hsub : C.sub d + 1 < a.srcs.length) (hn : ∀ e, C.next d e = some (some dn))
    (hpc : C.pc dn = C.pc d) (hs : C.sub dn = C.sub d + 1) (ha : C.acc dn = C.acc d)
    (hF : C.facts dn = C.facts d) (hinv : C.inv d → C.inv dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_st hk hf
  rw [afterStore_mid (by rw [h.2.1]; exact hsub)]
  refine .inl (.inr ⟨dn, _, hn _, .refl, ⟨?_, ?_, ?_, h.2.2.2.1, ?_⟩, hinv hi⟩)
  · exact h.1.trans hpc.symm
  · show t.sub + 1 = C.sub dn
    rw [h.2.1, hs]
  · exact h.2.2.1.trans ha.symm
  · rw [hF]; exact h.2.2.2.2

/-- The last element of a vector store (or a scalar store): the thread continues at the next
instruction, from where the local code leads to the successor `dn`. -/
theorem step_vec_last {d dn : C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .store)
    (hsub : ¬ C.sub d + 1 < a.srcs.length) (hn : ∀ e, C.next d e = some (some dn))
    (ha : C.acc d = []) (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_st hk hf
  rw [afterStore_last (by rw [h.2.1]; exact hsub)]
  exact hl.cont hi (hn _)
    ⟨by simp [h.1], rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩

/-- A ballot vote of the predicate fact `(p, pv)` into register `dv`, whose machine records the
ballot. -/
theorem step_vote {d : C.D} {dok : BitVec 32 → C.D} {gd : Option (Nat × Bool)}
    {ty : Option DType} {dv p : Nat} {neg pv : Bool} {mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.vote .ballot neg, ty, [some dv], [.reg p],
      some mask⟩⟩)
    (hpv : (p, .pred pv) ∈ C.facts d) (hr : ∀ q ∈ C.facts d, q.1 ≠ dv)
    (hn : ∀ m b, C.next d ⟨C.pc d, .vote m (pv != neg) b⟩ = some (some (dok b)))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ b : BitVec 32, C.Lands d (C.pc d + 1)
      ((dv, .bits 32 (BitVec.ofNat 64 b.toNat)) :: C.facts d) (dok b)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  have hp : readPred L g t (.reg p) = .ok pv := by
    have hm := holds_mem h0.2.2.2.2 hpv
    simp [readPred, readReg, hm, bind, Except.bind, pure, Except.pure]
  obtain ⟨m, b, rfl, rfl⟩ := fires_vote hp hf
  exact (hl b).cont hi (hn m b) (At.set h0 hr)

/-- `ret` and `exit` fire no event that continues. -/
theorem step_exit {d : C.D} {gd : Option (Nat × Bool)} {op : Op}
    (hc0 : K.code[C.pc d]? = some ⟨gd, op⟩) (hop : op = .ret ∨ op = .exit) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  rcases hop with rfl | rfl <;> simp [eventTmpl, Fires] at hf

end
end PTX.Flow.Code
