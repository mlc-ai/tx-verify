-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions
public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.WordRead
public meta import Lean

@[expose] public section

/-! # Generic thread-layer lemmas and tactics the library does not have

Candidates for `Lemmas/Flow/Step/` (nothing here names the kernel except the last section):

* `seg_ldParam`: a scalar `ld.param` as a one-step segment from a launch fact
  `L.params p = some x` (the library has the step, `exec_ldParam`, but no `Seg` form; a segment's
  evaluation cannot read `L.params` of a symbolic launch).
* `step_elect_rec`: the election combinator whose successors are functions of the elected lane
  (`Code.step_elect` fixes one successor per outcome, so a machine cannot record the leader).
* `lands_cut`: a successor reached through a checkpoint with stated facts.
* `seg_setp_word`, `dead_setp_noWord`: the first integer read (`setp` against an immediate) of
  a register holding any value an event returned: one step on its word (`wordOf`), or death.
* `shfl_word_step`: the step of a shuffle (with validity predicate) whose value that `setp`
  reads: continue with the word, or stop at a dead thread; the machine never gives up.
* `elect_step`: the `.elect` branch of `site_step` with `step_elect_rec` and a cut after the
  election's guarded moves.

The last section proves, for this kernel's assumption list, that no assumption takes a segment
(`segFree`) and gives `seg_sym` its two side-goal tactics (`sym_local_none`, `sym_seg_free`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX PTX.Proof PTX.Flow

noncomputable section

section Generic

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A scalar `ld.param` as a one-step segment**: the destination holds the parameter's bits,
given that the launch passes the parameter (`hx`), that no assumption gives the instruction a
rule (`hL`) and that none takes a segment there (`hA`). -/
theorem seg_ldParam {pc d w : Nat} {p : String} {x : BitVec 64} {ty : DType}
    {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }⟩)
    (hx : L.params p = some x) (hd : ∀ r ∈ F, r.1 ≠ d)
    (hL : NoRuleAt A L g pc (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }))
    (hA : Assumption.SegFreePc A pc) (hw : ty.width = w := by rfl)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] } = some .threadMove := by rfl) :
    Seg K A L g 1 pc F (pc + 1) ((d, .bits w (truncBits w x)) :: F) := by
  intro t h
  exact ⟨_, run_local hc rfl h
    (exec_ldParam hx (Assumption.SegFreePc.of_eq h.1 hA) (hL t h.1) hw hr), At.set h hd⟩

/-- **`setp` of a register that holds any value with a word, against an immediate**, as a
one-step segment: the comparison of the word (`wordOf`, the integer an integer instruction reads
from the value), whatever kind of value the register holds. The first integer read of a value an
event returned (a shuffle's, a load's) goes through this lemma, so that the machine need not
restrict the kind of the value. -/
theorem seg_setp_word {pc d r w : Nat} {c : Cmp} {k : IType} {imm : Int} {v : Value} {n : Nat}
    {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none,
      .int ⟨.setp c none, .int k w, false, [some d], [.reg r, .imm imm]⟩⟩)
    (hr : (r, v) ∈ F) (hn : wordOf v = some n) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : NoRuleAt A L g pc
      (.int ⟨.setp c none, .int k w, false, [some d], [.reg r, .imm imm]⟩))
    (hA : Assumption.SegFreePc A pc)
    (hrule : IntInstr.rule ⟨.setp c none, .int k w, false, [some d], [.reg r, .imm imm]⟩ =
      some .threadInt := by rfl) :
    Seg K A L g 1 pc F (pc + 1)
      ((d, .pred (compare c k w (truncBits w (BitVec.ofNat 64 n))
        (truncBits w (BitVec.ofInt 64 imm)))) :: F) := by
  intro t h
  have hreg := holds_mem h.2.2.2.2 hr
  have he : execLocalA A L g t
      (.int ⟨.setp c none, .int k w, false, [some d], [.reg r, .imm imm]⟩) =
      .ok (PTX.next (setReg t d (.pred (compare c k w (truncBits w (BitVec.ofNat 64 n))
        (truncBits w (BitVec.ofInt 64 imm)))))) := by
    rw [execLocalA_core hL hA h.1, execLocal_int hrule]
    simp [execInt, DType.width, DType.kind?, readBits_word hreg hn, PTX.Flow.readBits_imm, bind,
      Except.bind, pure, Except.pure]
  exact ⟨_, run_local hc rfl h he, At.set h hd⟩

/-- **`setp` of a register that holds a value without a word kills the thread** (a pointer, a
cache policy, a value without a bit pattern: the integer read faults). -/
theorem dead_setp_noWord {pc d r w : Nat} {c : Cmp} {k : IType} {imm : Int} {v : Value}
    {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none,
      .int ⟨.setp c none, .int k w, false, [some d], [.reg r, .imm imm]⟩⟩)
    (hr : (r, v) ∈ F) (hn : wordOf v = none)
    (hL : NoRuleAt A L g pc
      (.int ⟨.setp c none, .int k w, false, [some d], [.reg r, .imm imm]⟩))
    (hA : Assumption.SegFreePc A pc)
    (hrule : IntInstr.rule ⟨.setp c none, .int k w, false, [some d], [.reg r, .imm imm]⟩ =
      some .threadInt := by rfl) :
    DeadFrom K A L g pc F := by
  refine DeadFrom.local_error hc rfl fun R cf hR => ?_
  obtain ⟨f, hf⟩ := readBits_noWord (L := L) (g := g) (t := ⟨pc, R, cf, 0, [], none⟩) (w := w)
    (holds_mem hR hr) hn
  refine ⟨f, ?_⟩
  rw [execLocalA_core hL hA rfl, execLocal_int hrule]
  simp [execInt, DType.width, hf, bind, Except.bind]

/-- The keys of facts with one more explicit fact in front are apart from `d`. -/
theorem keys_cons {F : List (Nat × Value)} {d k : Nat} {v : Value} (hk : k ≠ d)
    (h : ∀ q ∈ F, q.1 ≠ d) : ∀ q ∈ (k, v) :: F, q.1 ≠ d := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hk
  · exact h q hq

variable {C : Code K A L g}

/-- An election into predicate `p` and, if `dst` names one, the leader register, whose machine
records the elected lane: the elected lane continues to `dl ld`, the others to `ds ld`
(`Code.step_elect` with successors that depend on the leader). -/
theorem step_elect_rec {d : C.D} {dl ds : Nat → C.D} {gd : Option (Nat × Bool)}
    {ty : Option DType} {dst : Option Nat} {p : Nat} {mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.elect, ty, [dst, some p], [], some mask⟩⟩)
    (hp : ∀ q ∈ C.facts d, q.1 ≠ p)
    (hd : ∀ r ∈ dst, (∀ q ∈ C.facts d, q.1 ≠ r) ∧ r ≠ p)
    (hnl : ∀ mk inst ld, laneOf L g = ld →
      C.next d ⟨C.pc d, .elect mk inst ld⟩ = some (some (dl ld)))
    (hns : ∀ mk inst ld, laneOf L g ≠ ld →
      C.next d ⟨C.pc d, .elect mk inst ld⟩ = some (some (ds ld)))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hll : ∀ ld, C.Lands d (C.pc d + 1)
      ((p, .pred true) :: Code.electFacts dst ld (C.facts d)) (dl ld))
    (hls : ∀ ld, C.Lands d (C.pc d + 1)
      ((p, .pred false) :: Code.electFacts dst ld (C.facts d)) (ds ld)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := Code.at_of_atD h hs ha
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  have h1 : ∃ t1, At t1 (C.pc d) (Code.electFacts dst ld (C.facts d)) ∧
      (dst.elim t fun r => setReg t r (.bits 32 (BitVec.ofNat 64 ld))) = t1 := by
    cases dst with
    | none => exact ⟨t, h0, rfl⟩
    | some r =>
      obtain ⟨hr, -⟩ := hd r rfl
      exact ⟨setReg t r (.bits 32 (BitVec.ofNat 64 ld)), ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1,
        Function.update_self .., holds_update h0.2.2.2.2 hr⟩, rfl⟩
  obtain ⟨t1, ht1, he⟩ := h1
  rw [he]
  have hp' : ∀ q ∈ Code.electFacts dst ld (C.facts d), q.1 ≠ p := by
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

/-- **A successor reached through a cut**: a segment to the checkpoint `q` with the facts `H`,
then the successor from there. -/
theorem lands_cut {d d' : C.D} {s q : Nat} {F H : List (Nat × Value)}
    (h1 : ∃ n, Seg K A L g n s F q H) (h2 : C.Lands d q H d') : C.Lands d s F d' :=
  ⟨fun hi => Seg.comp_ex h1 (h2.seg hi), h2.sub, h2.acc, h2.inv⟩

end Generic

/-- `elect_step q H trans [lemmas] seg_by (tac) inv_by (tac) guard_by (tac)`: the
obligation `C.StepAt d` of a literal election site whose successors record the elected lane
(`step_elect_rec`). The code after an election starts with guarded moves (`@%px mov.s32 %r, 1`),
which `seg_sym` does not walk; each successor's segment is cut at `q`, after them, with the facts
`H ld b` (`ld` the elected lane, `b` whether this lane is it): the piece to `q` is evaluated
(`seg_auto`, the guard being a literal there) and the rest goes as at any site (`lands_auto`). -/
syntax "elect_step " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " seg_by " "(" tacticSeq ")" " inv_by " "(" tacticSeq ")" " guard_by " "(" tacticSeq ")" :
  tactic

macro_rules
  | `(tactic| elect_step $q $H trans [$ls,*] seg_by ($seg) inv_by ($inv)
      guard_by ($gd)) =>
    `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event ($gd)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_elect_rec (dl := ?dl) (ds := ?ds)
        ?hc ?hp ?hd ?hnl ?hns ?hs ?ha ?hll ?hls)
      case hc => code_lookup
      case hs => rfl
      case ha => rfl
      case hp => fact_free
      case hd =>
        intro r hr
        first | (cases hr; done) | (cases hr; exact ⟨by fact_free, by decide⟩)
      case hnl => intro mk inst ld hld; next_simp [hld, $ls,*]
      case hns => intro mk inst ld hld; next_simp [hld, $ls,*]
      case hll =>
        intro ld
        refine PTX.Kernels.FlashKdaFwd.Proof.Thread.lands_cut (q := $q) (H := $H ld true) ?_ ?_
        · site_norm
          dsimp only [PTX.Flow.Code.electFacts]
          seg_auto using $seg
        · lands_auto ($seg) ($inv)
      case hls =>
        intro ld
        refine PTX.Kernels.FlashKdaFwd.Proof.Thread.lands_cut (q := $q) (H := $H ld false) ?_ ?_
        · site_norm
          dsimp only [PTX.Flow.Code.electFacts]
          seg_auto using $seg
        · lands_auto ($seg) ($inv)))

/-- `shfl_word_step trans [lemmas] seg_by (tac) inv_by (tac) guard_by (tac)`: the obligation
`C.StepAt d` of a literal shuffle site with a validity predicate whose received value the code
reads once, by the `setp` (register against immediate) right after the shuffle. The machine's
transition is `match wordOf v with | some n => some (some _) | none => none`: a value with a
word continues (the `setp` is one step by `seg_setp_word`, the rest as at any site), any other
value is dead at the `setp` (`dead_setp_noWord`). `site_step` has no branch for a shuffle with
a dead outcome and a validity predicate. -/
syntax "shfl_word_step " "trans " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " seg_by " "(" tacticSeq ")" " inv_by " "(" tacticSeq ")" " guard_by " "(" tacticSeq ")" :
  tactic

macro_rules
  | `(tactic| shfl_word_step trans [$ls,*] seg_by ($seg) inv_by ($inv) guard_by ($gd)) =>
    `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event ($gd)
      refine' (PTX.Flow.Code.step_shfl_valid (nv := ?nv) ?hc ?hr ?hp ?hrp ?hn ?hs ?ha ?hdead
        ?hl)
      case hc => code_lookup
      case hs => rfl
      case ha => rfl
      case hr => fact_free
      case hp => fact_free
      case hrp => decide
      case hn => intro m av bv cv recv ok; next_simp [$ls,*]; done
      case hdead =>
        intro v ok u hv
        beta_reduce at hv
        split at hv
        · cases hv
        · refine (show PTX.Flow.DeadFrom _ _ _ _ _ _ from ?_) u
          exact PTX.Kernels.FlashKdaFwd.Proof.Thread.dead_setp_noWord (by code_lookup)
            (List.mem_cons_of_mem _ List.mem_cons_self) (by assumption) (by sym_local_none)
            (by sym_seg_free)
      case hl =>
        intro v ok d' hv
        beta_reduce at hv
        split at hv
        · have hd := Option.some.inj (Option.some.inj hv)
          subst hd
          refine PTX.Kernels.FlashKdaFwd.Proof.Thread.lands_cut
            ⟨1, PTX.Kernels.FlashKdaFwd.Proof.Thread.seg_setp_word (by code_lookup)
              (List.mem_cons_of_mem _ List.mem_cons_self) (by assumption)
              (PTX.Kernels.FlashKdaFwd.Proof.Thread.keys_cons (by decide)
                (PTX.Kernels.FlashKdaFwd.Proof.Thread.keys_cons (by decide) (by fact_free)))
              (by sym_local_none) (by sym_seg_free)⟩ ?_
          try simp only [$ls,*]
          lands_auto ($seg) ($inv)
        · cases hv))

open Lean Meta Simp in
/-- `cmpLit`: a comparison of closed words (`PTX.compare c k w x y`, the term of `setp`, also
under the abbreviations `scmp`/`scmpi`) is its Boolean, by evaluation. A transition whose branch
condition is closed (a register the path set to a constant, compared with a constant) then has
no `if` for that branch. -/
dsimproc_decl cmpLit (PTX.compare _ _ _ _ _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← whnfD e
  if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false then return .done r
  return .continue

/-! ### The kernel's assumptions at the thread layer's instructions -/

/-- No assumption of the kernel takes a segment as one step (each element by the library's
`seg_free_elem`, whatever the length of the list). -/
theorem noSegments : Assumption.NoSegments Assumptions.all := by
  unfold Assumptions.all
  no_segments

/-- No assumption takes a segment at any program counter. -/
theorem segFree {pc : Nat} : Assumption.SegFreePc Assumptions.all pc :=
  noSegments.segFreePc

/-- `asms_none`: no assumption of the kernel gives the instruction of the goal
(`NoRuleAt Assumptions.all L g pc op`, `op` a literal instruction) a rule of its own: each
assumption's hook evaluated on the instruction, whatever the length of the list. It fails on
the forms `sharedBits` reads through the state (`shr.u64 _, _, 3`, `xor.b64` of two registers)
and on the float forms of `idealArith`, `approx` and `narrow`, which have their own step lemmas. -/
macro "asms_none" : tactic => `(tactic| (
  intro t _
  simp only [PTX.Kernels.FlashKdaFwd.Assumptions.all, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true]
  repeat' constructor
  all_goals rfl))

macro_rules | `(tactic| sym_local_none) => `(tactic| asms_none)

macro_rules
  | `(tactic| sym_seg_free) => `(tactic| exact PTX.Kernels.FlashKdaFwd.Proof.Thread.segFree)

end
end PTX.Kernels.FlashKdaFwd.Proof.Thread
