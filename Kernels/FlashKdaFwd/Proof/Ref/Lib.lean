-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Machine
public import Lemmas.Kernel.CountClosed
public import Lemmas.Kernel.UbLast
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeAsync
public import Lemmas.Flow.UbFree
public import Lemmas.Flow.MemTmpl
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section

/-! # Tools of the reference layer

The reference layer proves, phase by phase, an invariant of the states of a thread's machine
and reads facts about the thread's events off it. This file has what every phase uses; nothing
in it names a site.

* `Returned P X g`: what a thread's invariant has to know about the values its events return.
  An invariant that says where a thread is needs three facts from the layers above: an
  election over the full warp elects lane 0 (the assumption `electZero`; `returned_elect`), a
  shuffle of the warp index returns the warp index (every lane of a warp sends the same number;
  a source fact, a hypothesis here), and a load of an entry of the offsets array returns the
  launch content (the assumption `inputReadOnly` with `Pre.offsets`; `returned_offs`). The
  first and the third are proved here from consistency alone, without any machine: the
  tracking theorem of the thread layer rests on the third.
* `phase_inv`: the induction along a thread's states for one phase. An invariant `I k s` of
  the trace position and the state holds before every event of the thread until the phase's
  exit condition `E` held at an earlier position. Each step gets the concrete state, the
  instruction and the firing fact of the event (from the machine's soundness), and that the
  event is not undefined behaviour (an undefined-behaviour event is a thread's last, and the
  invariant is only claimed before an event). It does not use tracking (`Frame.Tracked`).
* `loadWord_some`, `loadWord_ne`, `elNext_some`, `elNextB_some`, `shNext_some`,
  `wtNext_some`: what a successor of one of the forms of `nextR_<site>` says about the event
  and the successor state.
* `reg_w`, `reg_p`: the value a concrete state holds in a register, from the
  machine's facts.
* `count_snoc`: one more event in a counted prefix.
* `file_simp`: the simp set that reads a rewritten register file at literal registers.
* `finVal`, `getLit`: simprocs that evaluate a closed `Fin` numeral's value and an entry of a
  closed table of numbers, so that a statement indexed by a position's ordinal reduces at a
  literal position.
* `ref_site [lemmas]`, `ref_facts [lemmas]`: the two phase-independent parts of a step's proof
  (the successor's site; a conjunction of register facts of the successor). A phase wraps
  `ref_facts` with the names of its own predicates (`Startup/Steps.lean`: `ref_pos`).
* `phase_event`: an event at a followed state, with the phase invariant or "the thread left
  the phase", and the concrete state and firing fact of the event. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### What the events of a thread return -/

/-- **The returned values an invariant of thread `g` relies on.** -/
structure Returned (P : Params) (X : Execution) (g : Nat) : Prop where
  /-- An election over the full warp elected lane 0. -/
  elect : ∀ {k pc inst ld : Nat}, X.get (g, k) = some ⟨pc, .elect 4294967295 inst ld⟩ → ld = 0
  /-- A shuffle returned a value whose word is the thread's warp index. -/
  shfl : ∀ {k pc b c : Nat} {md : ShflMode} {a v : Value} {ok : Bool},
    X.get (g, k) = some ⟨pc, .shfl md a b c v ok⟩ → wordOf v = some (warp g)
  /-- A load, at one of the 21 load instructions of the offsets array, of the eight bytes of
  entry `i` returned the entry. -/
  offs : ∀ {k pc i : Nat} {bs : List (Option Byte)}, i ≤ P.sequences →
    Assumptions.inputReadSites.contains pc = true → bs.length = 8 →
    X.get (g, k) = some ⟨pc, .rd { loc := P.offsetLoc i, size := 8 } bs⟩ →
      rebuild 3 bs = .ok (.bits 64 (W (firstToken P.length i)))

/-- The election field holds in every consistent execution (assumption `electZero`). -/
theorem returned_elect {K : Kernel} (hX : Consistent L K Assumptions.all mem0 X)
    {k pc inst ld : Nat} (h : X.get (g, k) = some ⟨pc, .elect 4294967295 inst ld⟩) : ld = 0 :=
  hX.asm Assumptions.electZero (by simp [Assumptions.all]) (g, k) pc inst ld h

/-- The name of parameter 15 in the assumption `inputReadOnly` is the specification's. -/
theorem offsetsParam_eq : Assumptions.offsetsParam = param "15" := by
  show Decoded.kernel.name ++ "_param_15" = Decoded.kernel.name ++ "_param_" ++ "15"
  rw [String.append_assoc]
  rfl

/-- Eight bytes that are the bytes of a 64-bit integer rebuild to it. -/
theorem rebuild_bits64 {bs : List (Option Byte)} {x : BitVec 64} (hl : bs.length = 8)
    (h : ∀ k < 8, bs[k]? = some (some ((Value.bits 64 x).byteAt k))) :
    rebuild 3 bs = .ok (.bits 64 x) := by
  have hb : bs = (Value.bits 64 x).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 8
    · rw [h k hk]
      simp [Value.toBytes, Value.bytes, hk]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by
        simp [Value.toBytes, Value.bytes]; omega)]
  rw [hb]
  exact rebuild_scalar (by simp [Value.bytes]) rfl

/-- **The offsets field holds in every consistent execution** under the precondition: the
assumption `inputReadOnly` says the eight bytes read are the launch bytes, and `Pre.offsets`
says the launch bytes of entry `i` are those of the integer `firstToken P.length i`. -/
theorem returned_offs {K : Kernel} (hpre : Pre P L mem0)
    (hX : Consistent L K Assumptions.all mem0 X) {e : EvId} {pc i : Nat}
    {bs : List (Option Byte)} (hi : i ≤ P.sequences)
    (hpc : Assumptions.inputReadSites.contains pc = true) (hl : bs.length = 8)
    (he : X.get e = some ⟨pc, .rd { loc := P.offsetLoc i, size := 8 } bs⟩) :
    rebuild 3 bs = .ok (.bits 64 (W (firstToken P.length i))) := by
  have hwf := hX.asm Assumptions.inputReadOnly (by simp [Assumptions.all]) e pc _ bs he hpc
  refine rebuild_bits64 hl fun k hk => ?_
  refine hwf k hk ⟨rfl, rfl, BitVec.ofNat 64 P.offsetsBase, ?_, ?_, ?_⟩ _ (hpre.offsets i hi k hk)
  · rw [offsetsParam_eq]; exact hpre.paramOffsets
  · have := offsets_lt hpre
    simp only [Params.offsetLoc, Loc.at, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have := offsets_lt hpre
    simp only [Params.offsetLoc, Loc.at, BitVec.toNat_ofNat, hpre.gridShape]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### The induction of one phase -/

/-- **A phase invariant along a thread's states.** -/
theorem phase_inv {K : Kernel} {A : List Assumption} {C : (g : Nat) → Flow.Code K A L g}
    (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    (I E : Nat → (C g).D → Prop) (h0 : I 0 (C g).init)
    (hs : ∀ (k : Nat) (e : Event) (s s' : (C g).D) (t : TState) (ins : Instr)
      (o : Option TState), X.get (g, k) = some e → Frame.stateAt C X g k = some (some s) →
      I k s → (C g).AtD s t → K.code[(C g).pc s]? = some ins →
      Fires ((C g).pc s) (eventTmpl A L g t ins.op) e o → (∀ pc f, e ≠ ⟨pc, .ub f⟩) →
      (C g).next s e = some (some s') → I (k + 1) s' ∨ E (k + 1) s') :
    ∀ k s, k < (X.tr g).length → Frame.stateAt C X g k = some (some s) →
      I k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt C X g j = some (some s0) ∧ E j s0 := by
  have key := Frame.stateAt_inv (C := C) (X := X) (g := g)
    (fun k s => k < (X.tr g).length →
      I k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt C X g j = some (some s0) ∧ E j s0)
    (fun _ => .inl h0) (by
      intro k e s s' he hσ hI hn hk1
      have hk : k < (X.tr g).length := by omega
      rcases hI hk with hI | ⟨j, hj, s0, h1, h2⟩
      · obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
        have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
          rintro pc f rfl
          obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k + 1]? = some e' :=
            ⟨_, List.getElem?_eq_getElem hk1⟩
          have := ub_last hX he he'
          omega
        rcases hs k e s s' t ins o he hσ hI hat hc hf hub hn with h | h
        · exact .inl h
        · have hσ' : Frame.stateAt C X g (k + 1) = some (some s') := by
            rw [Frame.stateAt_succ he, hσ]
            exact hn
          exact .inr ⟨k + 1, le_rfl, s', hσ', h⟩
      · exact .inr ⟨j, by omega, s0, h1, h2⟩)
  intro k s hk hσ
  exact key k s (by omega) hσ hk

/-- **An event of a phase**: the state before an event of a launched thread satisfies the
phase invariant, with the concrete state and the firing fact of the event, or the thread left
the phase (`hinv` is the phase's theorem, e.g. `startup_inv`). -/
theorem phase_event {K : Kernel} {A : List Assumption} {C : (g : Nat) → Flow.Code K A L g}
    (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    {I : Nat → (C g).D → Prop} {Past : Nat → Prop}
    (hinv : ∀ k s, k < (X.tr g).length → Frame.stateAt C X g k = some (some s) → I k s ∨ Past k)
    {k : Nat} {s : (C g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt C X g k = some (some s)) :
    (I k s ∧ ∃ t ins o, (C g).AtD s t ∧ K.code[(C g).pc s]? = some ins ∧
      Fires ((C g).pc s) (eventTmpl A L g t ins.op) e o) ∨ Past k := by
  rcases hinv k s (List.getElem?_eq_some_iff.mp he).1 hσ with h | h
  · obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
    exact .inl ⟨h, t, ins, o, hat, hc, hf⟩
  · exact .inr h

/-! ### The five forms of a successor -/

variable {e : Event} {d' : D}

theorem loadWord_some {f : BitVec 64 → D} (h : loadWord e f = some (some d')) :
    ∃ a bs x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok (.bits 64 x) ∧ d' = f x := by
  unfold loadWord at h
  split at h
  · rename_i a bs hk
    split at h
    · rename_i v hv
      unfold onWord64 at h
      split at h
      · rename_i y
        exact ⟨a, bs, y, hk, hv, (Option.some.inj (Option.some.inj h)).symm⟩
      · cases h
    · cases h
  · cases h

/-- **The give-up of the machine**: a load of the offsets array whose bytes rebuild to a
64-bit integer is followed. -/
theorem loadWord_ne {f : BitVec 64 → D} {a : Acc} {bs : List (Option Byte)} {y : BitVec 64}
    (hk : e.kind = .rd a bs) (hy : rebuild 3 bs = .ok (.bits 64 y)) :
    loadWord e f ≠ some none := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  rw [loadWord_rd hy, onWord64_bits]
  intro h
  cases h

theorem elNext_some {f : Nat → Bool → D} (h : elNext L g e f = some (some d')) :
    ∃ mask inst ld, e.kind = .elect mask inst ld ∧
      d' = f ld (decide (laneOf L g = ld)) := by
  unfold elNext at h
  split at h
  · rename_i mask inst ld hk
    refine ⟨mask, inst, ld, hk, ?_⟩
    have := Option.some.inj (Option.some.inj h)
    by_cases hl : laneOf L g = ld <;> simp [hl] at this ⊢ <;> exact this.symm
  · cases h

theorem elNextB_some {f : Nat → Bool → D} (h : elNextB L g e f = some (some d')) :
    ∃ mask inst ld, e.kind = .elect mask inst ld ∧ d' = f ld (laneOf L g == ld) := by
  unfold elNextB at h
  split at h
  · rename_i mask inst ld hk
    exact ⟨mask, inst, ld, hk, (Option.some.inj (Option.some.inj h)).symm⟩
  · cases h

theorem shNext_some {f : BitVec 64 → Bool → D} (h : shNext e f = some (some d')) :
    ∃ md a b c v ok n, e.kind = .shfl md a b c v ok ∧ wordOf v = some n ∧
      d' = f (BitVec.ofNat 64 n) ok := by
  unfold shNext at h
  split at h
  · rename_i md a b c v ok hk
    split at h
    · rename_i n hn
      exact ⟨md, a, b, c, v, ok, n, hk, hn, (Option.some.inj (Option.some.inj h)).symm⟩
    · cases h
  · cases h

theorem wtNext_some {f : Bool → D} (h : wtNext e f = some (some d')) :
    ∃ m q ok acq sc, e.kind = .wait m q ok acq sc ∧ d' = f ok := by
  unfold wtNext at h
  split at h
  · rename_i m q ok acq sc hk
    exact ⟨m, q, ok, acq, sc, hk, (Option.some.inj (Option.some.inj h)).symm⟩
  · cases h

theorem elNext_ne {f : Nat → Bool → D} : elNext L g e f ≠ some none := by
  unfold elNext
  split <;> (intro h; cases h)

theorem elNextB_ne {f : Nat → Bool → D} : elNextB L g e f ≠ some none := by
  unfold elNextB
  split <;> (intro h; cases h)

theorem shNext_ne {f : BitVec 64 → Bool → D} : shNext e f ≠ some none := by
  unfold shNext
  repeat' split
  all_goals (intro h; cases h)

theorem wtNext_ne {f : Bool → D} : wtNext e f ≠ some none := by
  unfold wtNext
  split <;> (intro h; cases h)

/-! ### Registers of a concrete state -/

/-- An integer register that is live at a state's site holds the file's word. -/
theorem reg_w {d : D} {t : TState} (hat : (code L g).AtD d t) {r : Nat}
    (hr : r ∈ Flow.live d.site.pc) {n : Nat} (hk : kind r = .word n) :
    t.regs r = some (.bits n (d.w r)) := by
  have h := regs_of_factsFrom hat.2.2.2.2 hr
  rw [h]
  simp only [valueOf, hk]

/-- A predicate register that is live at a state's site holds the file's Boolean. -/
theorem reg_p {d : D} {t : TState} (hat : (code L g).AtD d t) {r : Nat}
    (hr : r ∈ Flow.live d.site.pc) (hk : kind r = .pred) : t.regs r = some (.pred (d.p r)) := by
  have h := regs_of_factsFrom hat.2.2.2.2 hr
  rw [h]
  simp only [valueOf, hk]

/-! ### Counting along a trace -/

/-- One more event in a counted prefix. -/
theorem count_snoc (c : Event → Bool) {k : Nat} (he : X.get (g, k) = some e) :
    ((X.tr g).take (k + 1)).countP c = ((X.tr g).take k).countP c + (if c e = true then 1 else 0) :=
  Frame.countP_take_succ_ite c he

/-- An event that is not a barrier arrival is no `bar.sync 0`. -/
theorem isBarId_of_kind {id : Nat} (h : ∀ i c m, e.kind ≠ .bar i c m) :
    Execution.isBarId id e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> first | rfl | exact absurd rfl (h _ _ _)

/-- `file_simp [lemmas] at loc`: read rewritten register files at literal registers, with the
transition functions and the facts given as `lemmas`. -/
syntax "file_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic

macro_rules
  | `(tactic| file_simp $[$loc]?) => `(tactic| file_simp [] $[$loc]?)
  | `(tactic| file_simp [$ls,*] $[$loc]?) => `(tactic|
      simp only [PTX.Kernels.FlashKdaFwd.Proof.Thread.setW_apply,
        PTX.Kernels.FlashKdaFwd.Proof.Thread.setP_apply,
        PTX.Kernels.FlashKdaFwd.Proof.Thread.valueEx_apply, lookupLit, Option.getD_some,
        Option.getD_none, $ls,*] $[$loc]?)

open Lean Meta Simp in
/-- `finVal`: the value of a closed `Fin` numeral (`((3 : Fin 11) : Nat)` is `3`), so that a
table indexed by a position's ordinal reduces at a literal position. -/
dsimproc_decl finVal (Fin.val _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← whnfD e
  let some n ← (Meta.evalNat r).run | return .continue
  return .done (mkNatLit n)

open Lean Meta Simp in
/-- `getLit`: an entry of a closed table of numbers (`[498, 501].getD 1 0` is `501`). -/
dsimproc_decl getLit (List.getD _ _ _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← whnfD e
  let some n ← (Meta.evalNat r).run | return .continue
  return .done (mkNatLit n)

/-- `ref_site [lemmas]`: the site of the successor state (`lemmas`: the transition function
and the decided branch conditions). -/
syntax "ref_site" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ref_site [$ls,*]) => `(tactic| (first
      | rfl
      | (file_simp [Bool.false_eq_true, ↓reduceIte, $ls,*]; done)
      | (file_simp [Bool.false_eq_true, ↓reduceIte, $ls,*]; rfl)))

/-- `ref_facts [lemmas]`: a conjunction of register facts of the successor state: unfold and
read the file (`lemmas`: the phase's predicates, the transition function, the decided branch
conditions, the facts of the old position, the closed forms), then normalize the 32-bit
arithmetic on words with the bounds in context (`w32_norm`). -/
syntax "ref_facts" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ref_facts [$ls,*]) => `(tactic| (
      (try file_simp [PTX.Kernels.FlashKdaFwd.Proof.Ref.finVal,
        PTX.Kernels.FlashKdaFwd.Proof.Ref.getLit, Bool.false_eq_true, ↓reduceIte, and_self,
        and_true, true_and, $ls,*]) <;>
      (try w32_norm) <;> (try simp only [and_self, and_true, true_and])))

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref
