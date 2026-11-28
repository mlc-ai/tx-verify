-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.Roles
public import Lemmas.Kernel.Progress.WarpCollPairU
public import Lemmas.Kernel.Progress.WarpNoBallotOp
import Lemmas.Flow.NotWarpColl
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Lib.Elect
import all Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.ElectOrdinal
import Lemmas.Kernel.Progress.WarpCls

@[expose] public section

/-! # The warp collectives of the code

The code's fifty-seven warp collectives are shuffles with immediate lane operands, elections with
the immediate full mask, and warp barriers. A state at one has the static part of its pc (`collS`),
and the facts of two lanes of a warp (`Sched.WarpPair`) give the kernel's `Sched.WarpCollRel`. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Descent

/-- The warp of a thread: its CTA and its warp rank. -/
def warpKey (L : Launch) (g : Nat) : Nat × Nat := (g / L.block, g % L.block / 32)

theorem warpKey_eq {L : Launch} {g h : Nat} (hs : SameWarp L g h) : warpKey L g = warpKey L h := by
  simp only [warpKey]; rw [hs.1.2.2, hs.2]

/-- The state of lane `g` is at a warp instruction. -/
def CollAt (Q : Params) (L : Launch) (g : Nat) (d : ((schedule Q L).code g).D) : Prop :=
  ∃ ins, kernel.code[((schedule Q L).code g).pc d]? = some ins ∧ opKind ins.op = .warp

/-- The static part of the warp instruction at a pc: its immediate operands, or the full election
mask. -/
def pcShape (pc : Nat) : Sched.CollShape :=
  (kernel.code[pc]?.bind fun i => opShape i.op).getD (.elect 4294967295)

noncomputable def collS (Q : Params) (L : Launch) (g : Nat)
    (d : ((schedule Q L).code g).D) : Sched.CollShape :=
  pcShape (((schedule Q L).code g).pc d)

private theorem warp_ck : kernel.code.all (fun ins => opKind ins.op != .warp ||
    ((opShape ins.op).isSome || electOp ins.op) && !ins.op.isLocal) = true := by
  decide +kernel

private theorem full_ck : kernel.code.all (fun ins => (opShape ins.op).all fun s =>
    match s with
    | .shfl .. => true
    | .elect mk | .warpBar mk | .vote mk => mk == 4294967295) = true := by
  decide +kernel

private theorem elect_ck : Lib.electMaskOk kernel.code = true := Lib.kernel_electMaskOk

/-- The code's elections have the shape of `elect_tmpl`. -/
private def electShape : Op → Bool
  | .warp ⟨.elect, _, [_, some _], [], some (.imm (-1))⟩ => true
  | .warp ⟨.elect, _, _, _, _⟩ => false
  | _ => true

private theorem elect_shape_ck : kernel.code.all (fun ins => electShape ins.op) = true := by
  decide +kernel

private theorem electShape_eq {op : Op} (h : electShape op = true) (he : electOp op = true) :
    ∃ ty d p, op = .warp ⟨.elect, ty, [d, some p], [], some (.imm (-1))⟩ := by
  cases op <;> try (simp [electOp] at he; done)
  rename_i w
  obtain ⟨kd, ty, ds, ss, mk⟩ := w
  cases kd <;> simp only [electOp, Bool.false_eq_true] at he
  rcases ds with _ | ⟨d1, _ | ⟨p, _ | ⟨_, _⟩⟩⟩ <;> rcases ss with _ | ⟨_, _⟩ <;>
    rcases mk with _ | ⟨_ | ⟨v⟩ | _⟩ <;> try (simp [electShape] at h; done)
  rcases p with _ | p
  · simp [electShape] at h
  by_cases hv : v = -1
  · subst hv; exact ⟨ty, d1, p, rfl⟩
  · simp [electShape, hv] at h

/-- An election with the immediate full mask has the full mask for its static part. -/
private theorem elect_tmpl {L : Launch} {g : Nat} {t : TState} {ty : Option DType}
    {d : Option Nat} {p : Nat} :
    (∃ f, warpTmpl L g t ⟨.elect, ty, [d, some p], [], some (.imm (-1))⟩ = .ub f) ∨
      Sched.tmplShape (warpTmpl L g t ⟨.elect, ty, [d, some p], [], some (.imm (-1))⟩) =
        some (.elect 4294967295) := by
  have h : warpTmpl L g t ⟨.elect, ty, [d, some p], [], some (.imm (-1))⟩ =
      electTmpl L g t d p (.imm (-1)) := rfl
  rw [h]
  have hr : readBits L g t 32 (.imm (-1)) = .ok 4294967295 := by
    simp [readBits, truncBits, pure, Except.pure]
  right
  have hm : electMember (4294967295 : BitVec 64).toNat (laneOf L g) := by
    have : (4294967295 : BitVec 64).toNat = 4294967295 := by decide
    rw [this]
    exact Sched.full_member (by unfold laneOf; omega)
  simp only [electTmpl, hr, hm, ↓reduceIte, Sched.tmplShape]
  rfl

/-- **A state at a warp instruction** has the static part of its pc: its instruction is no local
instruction, and its template is undefined behaviour or has that part, which is full. -/
theorem collS_shape {Q : Params} {L : Launch} {g : Nat} {d : ((schedule Q L).code g).D}
    (hd : CollAt Q L g d) : (collS Q L g d).Full ∧ ∀ t ins, ((schedule Q L).code g).AtD d t →
      ((schedule Q L).code g).inv d → kernel.code[((schedule Q L).code g).pc d]? = some ins →
      ins.op.isLocal = false ∧ ((∃ f, eventTmpl Assumptions.all L g t ins.op = .ub f) ∨
        Sched.tmplShape (eventTmpl Assumptions.all L g t ins.op) =
          some (collS Q L g d)) := by
  obtain ⟨ins0, hc0, hk⟩ := hd
  have key : ∀ ins, kernel.code[((schedule Q L).code g).pc d]? = some ins → ins = ins0 :=
    fun ins h => Option.some.inj (h.symm.trans hc0)
  have ck := List.all_eq_true.mp warp_ck ins0 (List.mem_of_getElem? hc0)
  simp only [hk, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at ck
  have fk := List.all_eq_true.mp full_ck ins0 (List.mem_of_getElem? hc0)
  have sh : collS Q L g d = (opShape ins0.op).getD (.elect 4294967295) := by
    simp [collS, pcShape, hc0]
  cases ho : opShape ins0.op with
  | some s =>
    simp only [ho, Option.getD_some] at sh
    simp only [ho, Option.all_some] at fk
    refine ⟨by rw [sh]; cases s <;> simp_all [Sched.CollShape.Full], fun t ins _ _ hi => ?_⟩
    obtain rfl := key ins hi
    exact ⟨ck.2, by rw [sh]; exact Sched.warpOp_tmpl ho⟩
  | none =>
    simp only [ho, Option.getD_none] at sh
    refine ⟨by rw [sh]; rfl, fun t ins _ _ hi => ?_⟩
    obtain rfl := key ins hi
    refine ⟨ck.2, ?_⟩
    have he : electOp ins.op = true := by simpa [ho] using ck.1
    have es := List.all_eq_true.mp elect_shape_ck ins (List.mem_of_getElem? hc0)
    obtain ⟨gd, op⟩ := ins
    obtain ⟨ty, d1, p, rfl⟩ := electShape_eq es he
    rw [sh]
    exact elect_tmpl (L := L) (g := g) (t := t) (ty := ty) (d := d1) (p := p)

/-- A warp instruction's template is undefined behaviour or has the static part of its pc. -/
theorem warp_tmpl_shape {L : Launch} {g : Nat} {t : TState} {pc : Nat} {ins : Instr}
    (hc : kernel.code[pc]? = some ins) (hk : opKind ins.op = .warp) :
    (∃ f, eventTmpl Assumptions.all L g t ins.op = .ub f) ∨
      Sched.tmplShape (eventTmpl Assumptions.all L g t ins.op) = some (pcShape pc) := by
  have ck := List.all_eq_true.mp warp_ck ins (List.mem_of_getElem? hc)
  simp only [hk, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at ck
  have sh : pcShape pc = (opShape ins.op).getD (.elect 4294967295) := by simp [pcShape, hc]
  cases ho : opShape ins.op with
  | some s =>
    rw [sh, ho]
    exact Sched.warpOp_tmpl (A := Assumptions.all) (L := L) (g := g) (t := t) ho
  | none =>
    have he : electOp ins.op = true := by simpa [ho] using ck.1
    have es := List.all_eq_true.mp elect_shape_ck ins (List.mem_of_getElem? hc)
    rw [sh, ho]
    obtain ⟨gd, op⟩ := ins
    obtain ⟨ty, d1, p, rfl⟩ := electShape_eq es he
    exact elect_tmpl (L := L) (g := g) (t := t) (ty := ty) (d := d1) (p := p)

private theorem fires_notColl {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : NotColl m) (hf : Fires pc m e o) : Sched.isWarpColl e = false := by
  obtain ⟨epc, ek⟩ := e
  cases m <;> simp only [NotColl] at hm <;> simp only [Fires] at hf <;>
    aesop (add norm simp [Sched.isWarpColl])

/-- A warp collective event is fired by a warp instruction. -/
theorem coll_warp_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t op) e o) (hc : Sched.isWarpColl e = true) :
    opKind op = .warp := by
  by_contra hne
  have hop : isWarpOp op = false := by
    cases op <;> simp_all [isWarpOp, opKind]
  have := fires_notColl (eventTmpl_notColl (A := A) (L := L) (g := g) (t := t) hop) hf
  rw [hc] at this
  cases this

private theorem fires_coll_of_shape {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hf : Fires pc m e o) (hs : (Sched.tmplShape m).isSome = true) :
    Sched.isWarpColl e = true := by
  obtain ⟨epc, ek⟩ := e
  cases m <;> simp only [Sched.tmplShape, Option.isSome_none, Bool.false_eq_true] at hs <;>
    simp only [Fires] at hf <;> aesop (add norm simp [Sched.isWarpColl])

/-- The instruction at a pc is a warp instruction. -/
def isWarpAt (pc : Nat) : Bool := kernel.code[pc]?.any fun ins => opKind ins.op == .warp

/-- **A clean event fired from an instruction is a warp collective** exactly when the instruction
is a warp instruction. -/
theorem fired_coll {L : Launch} {g pc : Nat} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (code : kernel.code[pc]? = some ins)
    (fire : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (nu : ∀ f, e.kind ≠ .ub f) :
    Sched.isWarpColl e = isWarpAt pc := by
  unfold isWarpAt
  rw [code, Option.any_some]
  by_cases hk : opKind ins.op = .warp
  · simp only [hk, beq_self_eq_true]
    rcases warp_tmpl_shape (L := L) (g := g) (t := t) code hk with ⟨f, hf⟩ | hs
    · rw [hf] at fire
      exact absurd (by rw [fire.1]) (nu f)
    · exact fires_coll_of_shape fire (by rw [hs]; rfl)
  · have hop : isWarpOp ins.op = false := by
      cases h : ins.op <;> simp_all [isWarpOp, opKind]
    have := fires_notColl (eventTmpl_notColl (A := Assumptions.all) (L := L) (g := g)
      (t := t) hop) fire
    rw [this]
    cases h : (opKind ins.op == .warp)
    · rfl
    · exact absurd (beq_iff_eq.mp h) hk

/-- **An event of a consistent execution is a warp collective** exactly when its instruction is
a warp instruction. -/
theorem warp_event {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get i = some e) (nu : ∀ f, e.kind ≠ .ub f) :
    Sched.isWarpColl e = isWarpAt e.pc := by
  obtain ⟨f, bad⟩ | ⟨t, ins, o, -, code, fire⟩ := get_source hX get
  · exact (nu f bad).elim
  exact fired_coll code fire nu

/-- **A warp collective event has the static part of its pc.** -/
theorem warp_kind {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get i = some e) (hc : Sched.isWarpColl e = true) :
    Sched.kindShape e.kind = some (pcShape e.pc) := by
  obtain ⟨f, bad⟩ | ⟨t, ins, o, -, code, fire⟩ := get_source hX get
  · obtain ⟨pc, kd⟩ := e
    simp only at bad
    subst bad
    simp [Sched.isWarpColl] at hc
  have hk : opKind ins.op = .warp := coll_warp_op fire hc
  obtain ⟨s, hs, hk'⟩ := Sched.fires_shape fire hc
  rcases warp_tmpl_shape (L := L) (g := i.1) (t := t) code hk with ⟨f, hf⟩ | h
  · rw [hf] at hs; simp [Sched.tmplShape] at hs
  · rw [hs] at h; cases h; exact hk'

/-- **The kernel's warp-collective facts** from the facts of two lanes of a warp. -/
theorem warp_rel {Q : Params} {L : Launch} {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hpairs : ∀ {g h : Nat}, SameWarp L g h →
      Sched.WarpPair m (schedule Q L) X (CollAt Q L) (collS Q L) g h) :
    Sched.WarpCollRel m (schedule Q L) X (warpKey L) (CollAt Q L) := by
  refine Sched.warpCollRel_of_pairsU (S := collS Q L)
    (fun {g h} hg hh hk => ⟨⟨hg, hh, congrArg Prod.fst hk⟩, congrArg Prod.snd hk⟩)
    (fun _ _ => thread_sound hp ‹_›) hX (fun {g k d} hg hpos => ?_) hpairs
  have hd : CollAt Q L g d := by
    rcases hpos.2 with ⟨e, he, hc⟩ | ⟨-, hat⟩
    · have hu : ∀ f, e.kind ≠ .ub f := fun f hf => by
        obtain ⟨pc, kd⟩ := e
        simp only at hf
        subst hf
        simp [Sched.isWarpColl] at hc
      obtain ⟨t, ins, o, -, -, hins, hf⟩ :=
        Frame.fired_siteU (C := thread Q L) (fun _ hg => thread_sound hp hg) hX he hpos.1 hu
      exact ⟨ins, hins, coll_warp_op hf hc⟩
    · exact hat
  exact collS_shape hd

end PTX.Kernels.InklingRelDecode.Proof
