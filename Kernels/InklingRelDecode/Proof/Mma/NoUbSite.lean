-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.NoUbStep
public import Kernels.InklingRelDecode.Proof.Mma.NoUbIssue
public import Kernels.InklingRelDecode.Proof.Mma.Ref
import Kernels.InklingRelDecode.Proof.Mma.Shape
import Kernels.InklingRelDecode.Proof.Mma.Steps
import Kernels.InklingRelDecode.Proof.Mma.StepsRead
import Kernels.InklingRelDecode.Proof.Mma.StepsIssue
import Kernels.InklingRelDecode.Proof.Mma.Commit
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Kernels.InklingRelDecode.Gen.StepDispatch
import Lemmas.Flow.NoUbSites
import Lemmas.Flow.UbStop
import Lemmas.Flow.SharedSymOk
import Lemmas.Flow.TmplOkSync
import Lemmas.Flow.ReadLive
import Lemmas.Flow.Next
import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # The sites of the MMA warp are not undefined behaviour: strict steps, templates, no death. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {regs : Nat → Value} {w : Value}
  {t : TState}

/-- **Every site of the MMA warp steps strictly** along the reference: the recorded base word
and the loop bound have bit patterns, and so has every word a broadcast delivers. -/
theorem stepFor_site {n : Nat} {d : D} (hp : Pre Q L m) (hw : w.regBits.isSome) (hr : Ref n d)
    (e : Event)
    (typed : ∀ a b c x ok, (e = ⟨Flow.shfl_13, .shfl .idx a b c x ok⟩ ∨
      e = ⟨Flow.shfl_14, .shfl .idx a b c x ok⟩) → x.regBits.isSome) :
    (code L g regs w).StepFor d e := by
  obtain ⟨s, i, v⟩ := d
  cases s with
  | setMaxReg => exact (dec_step i v).stepFor e
  | ldNum => exact (iter_read_step i v).stepFor e
  | bar0 => exact bar0_for hp i v e (hr rfl).1 hw
  | qkBar => exact (kv_bar_step i v).stepFor e
  | kvWait => exact (kv_poll_step i v).stepFor e
  | qkShfl => exact qk_broadcast_for i v e (fun a b c x ok h => typed a b c x ok (.inl h))
  | qkBar2 => exact qk_prepare_for hp i v e hw
  | qkSkip => exact qk_skip_for hp i v e (hr rfl).1
  | qkElect => exact qk_election_for hp i v e (hr rfl).1
  | qk j => exact (qk_issue_step hp j i v).stepFor e
  | qkCommit => exact qk_notify_for hp i v e (hr rfl).1
  | pvBar => exact (p_bar_step i v).stepFor e
  | pWait => exact (p_poll_step i v).stepFor e
  | pvShfl => exact pv_broadcast_for i v e (fun a b c x ok h => typed a b c x ok (.inr h))
  | pvBar2 => exact pv_prepare_for hp i v e hw
  | pvSkip => exact pv_skip_for hp i v e (hr rfl).1
  | pvElect => exact pv_election_for hp i v e (hr rfl).1
  | pv j => exact (pv_issue_step hp j i v).stepFor e
  | pvCommit1 => exact (pv_notify_step hp i v).stepFor e
  | pvCommit2 => exact pv_done_for hp i v e (hr rfl).1
  | finBar => exact (final_bar_step i v).stepFor e
  | finElect => exact (final_elect_step hp i v).stepFor e
  | finCommit => exact (final_commit_step i v).stepFor e
  | bar1 => exact (return_bar_step i v).stepFor e
  | setMaxRegInc => exact (inc_step i v).stepFor e
  | dispatch => exact fun _ _ _ _ _ => .inl (.inl rfl)

private theorem site_commit (hp : Pre Q L m) (hg : g < L.threads) (s : CommitSite) {i : Nat}
    {v : Value} {ins : Instr} (hat : (code L g regs w).AtD ⟨s.site, i, v⟩ t)
    (hc : kernel.code[s.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  refine not_ub_of_fires (pc := s.site.pc) (fun f' hf => ?_) f
  have := commit_shape hp hg s hat hc hf
  cases this

/-- **The template of a site of the MMA warp is not undefined behaviour**, at a state that holds
its facts, in a lane of the grid, with the base word zero and a warp index with a bit pattern. -/
theorem safe_site (hp : Pre Q L m) (hg : g < L.threads) (hw : w = b32 0)
    (h464 : ∃ x, regs 464 = .bits 32 x) {d : D} {ins : Instr}
    (hat : (code L g regs w).AtD d t) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s, i, v⟩ := d
  have reg464 (pc : Nat) (key : 464 ∈ Flow.live pc) (hs : (code L g regs w).pc ⟨s, i, v⟩ = pc) :
      ∃ x, t.regs 464 = some (.bits 32 x) := by
    obtain ⟨x, hx⟩ := h464
    obtain ⟨_, _, _, _, hR⟩ := hat
    refine ⟨x, ?_⟩
    have := holds_mem hR (mem_factsFrom (val := valueOf L regs w ⟨s, i, v⟩)
      (show 464 ∈ Flow.live ((code L g regs w).pc ⟨s, i, v⟩) by rw [hs]; exact key))
    rw [this]
    exact congrArg some hx
  cases s
  case setMaxReg =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2422)
    exact plainOk_tmpl hb (by decide) f
  case ldNum =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2423)
    have := hp.sharedAlignment
    have := hp.sharedRange
    refine ldSharedSym_ok (o := 0) rfl rfl rfl rfl rfl rfl (by decide) rfl (by decide) ?_ f
    simp only [wrapAddr, truncBits, DType.width]
    simp
    unfold sharedBytes at *
    omega
  case bar0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2424)
    exact barSync_imm_ok (by decide) f
  case qkBar =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2461)
    exact warpBar_ok f
  case kvWait =>
    have hc' : kernel.code[2462]? = some ins := hc
    refine not_ub_of_fires (pc := 2462) (fun f' hf => ?_) f
    obtain ⟨_, h⟩ := ready_poll (e := ⟨2462, .ub f'⟩) hp hat hc' hf
    cases h
  case qkShfl =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2464)
    obtain ⟨x, hx⟩ := reg464 2464 (by decide) rfl
    exact shfl_imm_ok (p := none) (Or.inr rfl) hb hx f
  case qkBar2 | qkSkip =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2466)
    exact warpBar_ok f
  case qkElect =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2477)
    exact elect_imm_ok f
  case qk j => exact qk_issue_ok hp hg hw j hat hc f
  case qkCommit => exact site_commit hp hg .qk hat hc f
  case pvBar =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2509)
    exact warpBar_ok f
  case pWait =>
    have hc' : kernel.code[2510]? = some ins := hc
    refine not_ub_of_fires (pc := 2510) (fun f' hf => ?_) f
    obtain ⟨_, h⟩ := p_poll (e := ⟨2510, .ub f'⟩) hp hat hc' hf
    cases h
  case pvShfl =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2512)
    obtain ⟨x, hx⟩ := reg464 2512 (by decide) rfl
    exact shfl_imm_ok (p := none) (Or.inr rfl) hb hx f
  case pvBar2 | pvSkip =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2514)
    exact warpBar_ok f
  case pvElect =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2525)
    exact elect_imm_ok f
  case pv j => exact pv_issue_ok hp hg hw j hat hc f
  case pvCommit1 => exact site_commit hp hg .empty hat hc f
  case pvCommit2 => exact site_commit hp hg .done hat hc f
  case finBar =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2550)
    exact warpBar_ok f
  case finElect =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2551)
    exact elect_imm_ok f
  case finCommit => exact site_commit hp hg .final hat hc f
  case bar1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2554)
    exact barSync_imm_ok (by decide) f
  case setMaxRegInc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2555)
    exact plainOk_tmpl hb (by decide) f
  case dispatch =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2337)
    exact plainOk_tmpl hb (by decide) f

private theorem cont_kind {pc : Nat} {op : Op} {v : Event} {o : Option TState}
    (hop : op ≠ .ret ∧ op ≠ .exit) (hf : Fires pc (eventTmpl Assumptions.all L g t op) v o)
    (hu : ∀ f, v.kind ≠ .ub f) {P : Event → Prop}
    (hs : ∀ u, Fires pc (eventTmpl Assumptions.all L g t op) v (some u) → P v) : P v :=
  shape_cont (P := fun e => (∀ f, e.kind ≠ .ub f) → P e) hf hop (fun u hf _ => hs u hf)
    (fun f hu' => absurd rfl (hu' f)) hu

/-- **The MMA warp dies only on the exit**: at a state of the warp, an event that is not
undefined behaviour has a successor (the word read is a 32-bit word, the polls wait, the
broadcasts shuffle, the elections elect). -/
theorem live_site (hp : Pre Q L m) {d : D} {ins : Instr} {o : Option TState} {v : Event}
    (hat : (code L g regs w).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) v o)
    (hu : ∀ f, v.kind ≠ .ub f)
    (rebuilds : d.site = .ldNum → ∀ ac bs, v.kind = .rd ac bs → ∃ x, rebuild 3 bs = .ok x) :
    next L g d v ≠ none := by
  obtain ⟨s, i, x⟩ := d
  have shfl (pc : Nat) (hc' : kernel.code[pc]? = some ins) {r : Nat}
      (hop : ins.op = .warp ⟨.shfl .idx, some (.int .b 32), [some r],
        [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩)
      (hf' : Fires pc (eventTmpl Assumptions.all L g t ins.op) v o) :
      ∃ a b c y ok, v.kind = .shfl .idx a b c y ok := by
    refine cont_kind (pc := pc) (P := fun e => ∃ a b c y ok, e.kind = .shfl .idx a b c y ok)
      (by rw [hop]; exact ⟨nofun, nofun⟩) hf' hu (fun u hf'' => ?_)
    rw [hop] at hf''
    obtain ⟨a, b, c, y, ok, rfl, -⟩ := fires_shfl (p := none) hf''
    exact ⟨a, b, c, y, ok, rfl⟩
  have elect (pc : Nat) {r q : Nat}
      (hop : ins.op = .warp ⟨.elect, none, [some r, some q], [], some (.imm (-1))⟩)
      (hf' : Fires pc (eventTmpl Assumptions.all L g t ins.op) v o) :
      ∃ mk inst ld, v.kind = .elect mk inst ld := by
    refine cont_kind (pc := pc) (P := fun e => ∃ mk inst ld, e.kind = .elect mk inst ld)
      (by rw [hop]; exact ⟨nofun, nofun⟩) hf' hu (fun u hf'' => ?_)
    rw [hop] at hf''
    obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf''
    exact ⟨mk, inst, ld, rfl⟩
  have opOf {pc : Nat} {c : Instr} (h : kernel.code[pc]? = some c)
      (hc' : kernel.code[pc]? = some ins) :
      ins.op = c.op := congrArg Instr.op (Option.some.inj (hc'.symm.trans h))
  cases s
  case ldNum =>
    obtain ⟨ac, bs, hk, hs⟩ := read_live (opOf Flow.code_2423 hc) rfl rfl rfl hf hu (rebuilds rfl)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    simp [next, hk, hy]
  case kvWait =>
    obtain ⟨ok, hk⟩ := ready_poll hp hat (hc : kernel.code[2462]? = some ins) hf
    simp only [next, hk]
    split <;> simp
  case pWait =>
    obtain ⟨ok, hk⟩ := p_poll hp hat (hc : kernel.code[2510]? = some ins) hf
    simp only [next, hk]
    split <;> simp
  case qkShfl =>
    obtain ⟨a, b, c, y, ok, hk⟩ := shfl 2464 hc (opOf Flow.code_2464 hc) hf
    simp [next, hk]
  case pvShfl =>
    obtain ⟨a, b, c, y, ok, hk⟩ := shfl 2512 hc (opOf Flow.code_2512 hc) hf
    simp [next, hk]
  case qkElect =>
    obtain ⟨mk, inst, ld, hk⟩ := elect 2477 (opOf Flow.code_2477 hc) hf
    simp only [next, hk]
    split <;> simp
  case pvElect =>
    obtain ⟨mk, inst, ld, hk⟩ := elect 2525 (opOf Flow.code_2525 hc) hf
    simp only [next, hk]
    split <;> simp
  case finElect =>
    obtain ⟨mk, inst, ld, hk⟩ := elect 2551 (opOf Flow.code_2551 hc) hf
    simp only [next, hk]
    split <;> simp
  all_goals simp [next]

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
