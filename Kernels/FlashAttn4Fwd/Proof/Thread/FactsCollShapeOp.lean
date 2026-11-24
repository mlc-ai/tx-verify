-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBase
public import Lemmas.Flow.CommitTarget

@[expose] public section

/-! # The static part of the kernel's warp collectives

Every warp-collective instruction of the kernel names its static operands as immediates: each
`shfl.sync` is `idx` with lane operands `0` and `31`, each `elect.sync` and `bar.warp.sync`
has the member mask `-1` (`collOpOk`, decided on the decoded code), and `vote.sync` has no rule
for another mask. So the static part of an instruction's template, when it is not undefined
behaviour, is a function of the instruction's opcode alone (`opShape`), and so of its position
(`pcShape`); every mask it names is the full one (`pcShape_full`). A thread at a warp-collective
state fires a template of that shape at the state's position (`out_shape`), and an event fired
from a followed state carries the shape of the state's position (`fired_shape`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross

noncomputable section

/-- The static part of the events of a warp-collective instruction. -/
def opShape : Op → Sched.CollShape
  | .warp ⟨.elect, _, _, _, _⟩ => .elect 4294967295
  | .warp ⟨.barWarp, _, _, _, _⟩ => .warpBar 4294967295
  | .warp ⟨.vote _ _, _, _, _, _⟩ => .vote 4294967295
  | _ => .shfl .idx 0 31

/-- The static part of the warp collective at a source position. -/
def pcShape (pc : Nat) : Sched.CollShape :=
  match kernel.code[pc]? with
  | some ins => opShape ins.op
  | none => .shfl .idx 0 31

theorem pcShape_full (pc : Nat) : (pcShape pc).Full := by
  unfold pcShape
  split
  · unfold opShape
    split <;> simp [Sched.CollShape.Full]
  · trivial

/-- An immediate operand of value `v`. -/
def isImm (o : Opnd) (v : Int) : Bool :=
  match o with
  | .imm x => x == v
  | _ => false

/-- The static operands of a warp-collective instruction are immediates: a shuffle is `idx`
from lane `0` over clamp `31`, an election's and a warp barrier's mask is `-1`. -/
def collOpOk : Op → Bool
  | .warp ⟨.shfl md, _, _, [_, b, c], _⟩ => md == .idx && isImm b 0 && isImm c 31
  | .warp ⟨.shfl _, _, _, _, _⟩ => false
  | .warp ⟨.elect, _, _, _, some mask⟩ => isImm mask (-1)
  | .warp ⟨.barWarp, _, _, _, some mask⟩ => isImm mask (-1)
  | _ => true

theorem kernel_collOpOk : kernel.code.all (fun ins => collOpOk ins.op) = true := by
  decide +kernel

theorem collOpOk_at {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins) :
    collOpOk ins.op = true :=
  List.all_eq_true.mp kernel_collOpOk ins (List.mem_of_getElem? hc)

theorem imm_eq {o : Opnd} {v : Int} (h : isImm o v = true) : o = .imm v := by
  cases o <;> simp_all [isImm]

/-- **The template of a warp-collective instruction** is undefined behaviour or has the
instruction's static part. -/
theorem eventTmpl_shape {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hw : kindOp .warp op = true) (hok : collOpOk op = true) :
    (∃ f, eventTmpl asms L g t op = .ub f) ∨
      Sched.tmplShape (eventTmpl asms L g t op) = some (opShape op) := by
  cases op <;> simp only [kindOp, Bool.false_eq_true] at hw
  rename_i w
  rcases w with ⟨kind, ty, dsts, srcs, mask⟩
  simp only [eventTmpl, warpTmpl]
  split
  -- `kindOp .warp` accepts no mode vote, reduction, match or `activemask`.
  all_goals try (exfalso; (try cases ‹VoteMode›) <;> simp_all; done)
  · rename_i md d p a b c mask' _ _ _ _ _
    simp only [collOpOk, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨rfl, hb⟩, hc⟩ := hok
    obtain rfl := imm_eq hb
    obtain rfl := imm_eq hc
    simp only [shflTmpl]
    repeat' split
    all_goals try exact .inl ⟨_, rfl⟩
    all_goals simp_all [readBits, truncBits, pure, Except.pure, Sched.tmplShape, opShape]
    all_goals subst_vars
    all_goals decide
  · simp only [voteTmpl]
    repeat' split
    all_goals try exact .inl ⟨_, rfl⟩
    all_goals simp_all [Sched.tmplShape, opShape]
  · rename_i d p mask' _ _ _ _ _
    simp only [collOpOk] at hok
    obtain rfl := imm_eq hok
    simp only [electTmpl, readBits, truncBits, pure, Except.pure]
    split
    · exact .inr rfl
    · exact .inl ⟨_, rfl⟩
  · rename_i mask' _ _ _ _ _
    simp only [collOpOk] at hok
    obtain rfl := imm_eq hok
    simp only [warpBarTmpl, readBits, truncBits, pure, Except.pure]
    split
    · exact .inr rfl
    · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩

/-- An event fired from a warp-collective template carries its static part. -/
theorem fires_shape {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} {s : Sched.CollShape}
    (hm : Sched.tmplShape m = some s) (hf : Fires pc m e o) : Sched.kindShape e.kind = some s := by
  cases m <;> simp only [Sched.tmplShape, reduceCtorEq] at hm
  all_goals simp only [Fires] at hf
  all_goals casesm* ∃ _, _, _ ∧ _
  all_goals subst_vars
  all_goals exact hm

/-- **A thread at a warp-collective state fires a template of its position's static part** at
that position, or undefined behaviour. -/
theorem out_shape {L : Launch} {g : Nat} {d : ThreadD} {t : TState} {m : Tmpl}
    (hat : (code L g).AtD d t) (hk : nextKind d = .warp)
    (hout : out kernel asms L g t = .ev m) :
    (∃ f, m = .ub f) ∨ (t.pc = (code L g).pc d ∧ Sched.tmplShape m = some (pcShape t.pc)) := by
  rcases out_ev hout with hub | ⟨ins, hc, rfl⟩
  · exact .inl hub
  have hpc : t.pc = (code L g).pc d := hat.1
  have hw := site_kindOp (L := L) (g := g) d (hpc ▸ hc)
  rw [hk] at hw
  rcases eventTmpl_shape (L := L) (g := g) (t := t) hw (collOpOk_at hc) with hub | hs
  · exact .inl hub
  · refine .inr ⟨hpc, ?_⟩
    rw [hs]
    simp only [pcShape, hc]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An event fired from a followed state at a warp collective carries the static part of the
state's position.** -/
theorem fired_shape (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hok : SitesTmplOk L) {g k : Nat} {d : ThreadD} {e : Event} (hg : g < L.threads)
    (hσ : St L X g k = some (some d)) (he : X.get (g, k) = some e)
    (hw : Sched.isWarpColl e = true) :
    nextKind d = .warp ∧ Sched.kindShape e.kind = some (pcShape ((code L g).pc d)) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hk : nextKind d = .warp := by
    have := (fired_kind hpre hX hok hg hσ he).1
    rw [hw] at this
    exact (beq_iff_eq.mp this.symm)
  refine ⟨hk, ?_⟩
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX he hσ
  have hkw := site_kindOp (L := L) (g := g) d hc
  rw [hk] at hkw
  rcases eventTmpl_shape (L := L) (g := g) (t := t) hkw (collOpOk_at hc) with ⟨f, hub⟩ | hs
  · exact absurd hub (hok g hg d t ins hat hinv hc f)
  · rw [fires_shape hs hf]
    simp only [pcShape, hc]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
