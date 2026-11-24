-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Assumption.Facts
public import Lemmas.Flow.Regs
public import Lemmas.Isa.Rule
public import Core.Assumption.TcLdDataflow

@[expose] public section

/-! # Register frames for trace comparison

These are derived properties of the local semantics. They let a kernel proof separate
registers controlling addresses and branches from registers carrying input data.
-/
namespace PTX.Proof
open PTX
noncomputable section

def writesRegs : Op → List Nat
  | .int i => i.dsts.filterMap id
  | .move m => m.dsts.filterMap id
  | .cvt c => [c.d]
  | .mem a => a.regs
  | .addr c => (Assumption.addrOperands c).2
  | .warp w => w.dsts.filterMap id
  | .float f => f.dsts.filterMap id
  | .misc (.createPolicy d _) => [d]
  | .clcQuery _ d _ => [d]
  | _ => []

/-- The registers of an operand. -/
def opndRegs : Opnd → List Nat
  | .reg r => [r]
  | _ => []

/-- The register of an address base. -/
def addrRegs : AddrBase → List Nat
  | .reg r _ => [r]
  | _ => []

/-- Every register an instruction names, one entry per mention, destinations included. -/
def opRegs : Op → List Nat
  | .int i => i.dsts.filterMap id ++ i.srcs.flatMap opndRegs
  | .move m => m.dsts.filterMap id ++ m.srcs.flatMap opndRegs
  | .cvt c => c.d :: c.srcs.flatMap opndRegs
  | .mem a => a.regs ++ addrRegs a.addr.base ++ a.srcs.flatMap opndRegs ++
      (a.hints.policy.map opndRegs).getD []
  | .addr c => (Assumption.addrOperands c).2 ++ (Assumption.addrOperands c).1.flatMap opndRegs
  | .warp w => w.dsts.filterMap id ++ w.srcs.flatMap opndRegs ++ (w.mask.map opndRegs).getD []
  | .float f => f.dsts.filterMap id ++ f.srcs.flatMap opndRegs
  | .misc (.createPolicy d _) => [d]
  | .misc (.nanosleep o) => opndRegs o
  | .misc .. => []
  | .matrix m => m.dsts ++ m.srcs.flatMap opndRegs ++
    (m.addr.map (fun a => addrRegs a.base)).getD []
  | .prefetchTensorMap _ _ a | .clcQuery _ _ a | .brx a _ _ => opndRegs a
  | .prefetchTensor m cs _ p => opndRegs m ++ cs.flatMap opndRegs ++ (p.map opndRegs).getD []
  | .setMaxReg .. | .cluster _ | .bra .. | .ret | .exit | .trap | .unmodeled _ | .bulkCommit
  | .bulkWait .. | .cpAsyncCommit | .cpAsyncWait ..
  | .fenceMbarInit | .tcRelinquish _ | .tcFenceBefore | .tcFenceAfter | .tcWaitLd | .tcWaitSt
  | .fence (.thread ..) => []
  | .fence (.proxy _ _ a) => (a.map (fun a => addrRegs a.base)).getD []
  | .cpAsyncArrive _ b _ _ | .tcShift _ b => [b]
  | .tcSt b as _ => b :: as.flatMap opndRegs
  | .barSync a _ => opndRegs a
  | .barSyncN a b _ | .barArrive a b _ | .tcDealloc _ a b => opndRegs a ++ opndRegs b
  | .cpTensor _ _ d _ m cs mb _ mc _ p =>
    d :: opndRegs m ++ cs.flatMap opndRegs ++ [mb] ++ (mc.map (opndRegs ·.2)).getD [] ++
      (p.map opndRegs).getD []
  | .cpTensorStore m cs s _ p _ _ =>
    opndRegs m ++ cs.flatMap opndRegs ++ [s] ++ (p.map opndRegs).getD []
  | .clcTryCancel _ d _ mb _ => [d, mb]
  | .mbarInit b _ c | .tcAlloc _ b _ c | .tcCp _ _ b c _ => b :: opndRegs c
  | .mbarInval b _ => [b]
  | .mbarArrive b _ tx c _ _ _ s => b :: opndRegs tx ++ opndRegs c ++ s.toList
  | .cpBulk c => c.dst :: c.src :: opndRegs c.size ++
    (c.mbar.map (fun m => m.1)).toList ++
    (c.multicast.map (fun m => m.1 :: opndRegs m.2)).getD [] ++
    (c.mask.map opndRegs).getD [] ++ (c.cachePolicy.map opndRegs).getD []
  | .asyncStore s => s.srcs.flatMap opndRegs ++ addrRegs s.addr.base ++
    (s.mbar.map (fun a => addrRegs a.base)).getD []
  | .cpAsync d _ s _ _ sr p => d :: s :: (match sr with
    | .full => []
    | .size n | .ignore n => opndRegs n) ++ (p.map opndRegs).getD []
  | .prefetchBulk s _ n p => s :: opndRegs n ++ (p.map opndRegs).getD []
  | .mbarWait d b _ par .. => d :: b :: opndRegs par
  | .tcMma m =>
    m.d :: (match m.a with | .smem d => opndRegs d | .tmem r _ => [r]) ++
      opndRegs m.bdesc ++ opndRegs m.idesc ++ m.mask.flatMap opndRegs ++ opndRegs m.enableD ++
      (m.zeroColumnMask.map opndRegs).getD []
  | .tcCommit _ b _ m => b :: (m.map opndRegs).getD []
  | .tcLd ds a _ _ => ds ++ [a]

def nextPc (op : Op) (pc : Nat) : Nat := match op with
  | .bra target _ => target
  | _ => pc + 1

/-- `pc` is an entry of the target list of a `brx.idx`. -/
def BrxTarget (op : Op) (pc : Nat) : Prop := match op with
  | .brx _ targets _ => pc ∈ targets
  | _ => False

structure LocalFrame (op : Op) (t t' : TState) : Prop where
  pc : t'.pc = nextPc op t.pc ∨ BrxTarget op t'.pc
  sub : t'.sub = t.sub
  acc : t'.acc = t.acc
  fault : t'.fault = t.fault
  regs : ∀ r, r ∉ writesRegs op → t'.regs r = t.regs r

private theorem frame_set {op : Op} {t : TState} {d : Nat} {v : Value}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op t (next (setReg t d v)) := by
  refine ⟨.inl hpc.symm, rfl, rfl, rfl, ?_⟩
  intro r hr
  exact Function.update_of_ne (by intro h; subst h; exact hr hd) _ _

/-- A step that writes a destination and the carry flag keeps the frame. -/
private theorem frame_setCarry {op : Op} {t : TState} {d : Nat} {v : Value} {cout c : Bool}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op t (next (setCarry (setReg t d v) cout c)) := by
  have hne : ∀ r, r ∉ writesRegs op → r ≠ d := by
    intro r hr h; subst h; exact hr hd
  refine ⟨.inl ?_, ?_, ?_, ?_, ?_⟩
  · simp only [next, setCarry]; split <;> exact hpc.symm
  · simp only [next, setCarry]; split <;> rfl
  · simp only [next, setCarry]; split <;> rfl
  · simp only [next, setCarry]; split <;> rfl
  · intro r hr
    simp only [next, setCarry]
    split <;> exact Function.update_of_ne (hne r hr) _ _

private theorem frame_set2 {op : Op} {t : TState} {d d' : Nat} {v v' : Value}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) (hd' : d' ∈ writesRegs op) :
    LocalFrame op t (next (setReg (setReg t d v) d' v')) := by
  refine ⟨.inl hpc.symm, rfl, rfl, rfl, ?_⟩
  intro r hr
  simp only [next, setReg]
  rw [Function.update_of_ne (by intro h; subst h; exact hr hd'),
    Function.update_of_ne (by intro h; subst h; exact hr hd)]

/-- `u` differs from `t` at most in the registers the instruction writes. -/
private def WritesOnly (op : Op) (t u : TState) : Prop :=
  u.pc = t.pc ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault ∧
    ∀ r, r ∉ writesRegs op → u.regs r = t.regs r

private theorem writesOnly_refl {op : Op} {t : TState} : WritesOnly op t t :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

private theorem writesOnly_setDst {op : Op} {t u : TState} {o : Option Nat} {v : Value}
    (h : WritesOnly op t u) (ho : ∀ r, o = some r → r ∈ writesRegs op) :
    WritesOnly op t (setDst u o v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases o with
  | none => exact ⟨h1, h2, h3, h4, h5⟩
  | some d =>
    refine ⟨h1, h2, h3, h4, fun r hr => ?_⟩
    simp only [setDst, setReg]
    rw [Function.update_of_ne (by intro e; subst e; exact hr (ho _ rfl))]
    exact h5 r hr

private theorem writesOnly_setReg {op : Op} {t u : TState} {d : Nat} {v : Value}
    (h : WritesOnly op t u) (hd : d ∈ writesRegs op) : WritesOnly op t (setReg u d v) :=
  writesOnly_setDst (o := some d) h (fun _ e => by cases e; exact hd)

private theorem frame_next {op : Op} {t u : TState} (hpc : nextPc op t.pc = t.pc + 1)
    (h : WritesOnly op t u) : LocalFrame op t (next u) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨.inl (by simp [next, h1, hpc]), h2, h3, h4, h5⟩


private def AllOk {α : Type} (P : α → Prop) : Exec α → Prop
  | .error _ => True
  | .ok v => P v

private theorem allOk_bind {α β : Type} {P : β → Prop} {r : Exec α} {f : α → Exec β}
    (h : ∀ a, AllOk P (f a)) : AllOk P (r >>= f) := by
  cases r with
  | error => trivial
  | ok a => exact h a

private theorem allOk_map {α β : Type} {P : α → Prop} {Q : β → Prop} {r : Exec α}
    {f : α → β} (h : AllOk P r) (hf : ∀ a, P a → Q (f a)) : AllOk Q (f <$> r) := by
  cases r with
  | error => trivial
  | ok a => exact hf a h

private theorem allOk_get {α : Type} {P : α → Prop} {r : Exec α}
    (h : AllOk P r) {v : α} (he : r = .ok v) : P v := by rw [he] at h; exact h

/-- Every outcome of an optional rule has the property. -/
private def AllOkO {α : Type} (P : α → Prop) (o : Option (Exec α)) : Prop :=
  ∀ e, o = some e → AllOk P e

private theorem allOkO_none {α : Type} {P : α → Prop} : AllOkO P (none : Option (Exec α)) :=
  fun _ he => nomatch he

private theorem allOkO_get {α : Type} {P : α → Prop} {o : Option (Exec α)}
    (h : AllOkO P o) {v : α} (he : o = some (.ok v)) : P v :=
  allOk_get (h _ he) rfl

private theorem allOkO_some {α : Type} {P : α → Prop} {e : Exec α} (h : AllOk P e) :
    AllOkO P (some e) :=
  fun _ he => by cases he; exact h

private theorem allOkO_bindRead {α β : Type} {P : β → Prop} {x : Option (Exec α)}
    {k : α → Option (Exec β)} (h : ∀ v, AllOkO P (k v)) : AllOkO P (Assumption.bindRead x k) := by
  intro e he
  cases x with
  | none => exact absurd he (by simp [Assumption.bindRead])
  | some ex =>
    cases ex with
    | error f => cases he; trivial
    | ok v => exact h v e (by simpa [Assumption.bindRead] using he)

/-- A list of value reads keeps the frame whatever its outcome. -/
private theorem allOk_mapM_bind {α β γ : Type} {P : α → Prop} {l : List β} {f : β → Exec γ}
    {k : List γ → Exec α} (h : ∀ v, AllOk P (k v)) : AllOk P (l.mapM f >>= k) := by
  cases hm : l.mapM f with
  | error e => trivial
  | ok v => exact h v

/-- A rule that only advances the source position keeps the frame. -/
private theorem frame_next_t {op : Op} {t : TState} (hpc : nextPc op t.pc = t.pc + 1) :
    LocalFrame op t (next t) :=
  ⟨.inl hpc.symm, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- The integer conversion arms write only the destination. -/
private theorem allOk_cvtInt {op : Op} {t : TState} {d dw sw : Nat} {dk sk : IType} {sat : Bool}
    {x : BitVec 64} {ext : MemExt}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    AllOk (LocalFrame op t)
      (match sat, sk, ext with
       | false, IType.u, MemExt.same => pure (next (setReg t d (.bits dw (truncBits dw x))))
       | sat, sk, ext =>
         pure (next (setReg t d (ext.extendBits dw (cvtIntBits sat dk dw sk sw x))))) := by
  cases sat <;> cases sk <;> cases ext <;> exact frame_set hpc hd

/-- A rule that branches keeps the frame when both outcomes do. -/
private theorem allOk_ite {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {a b : Exec α}
    (ha : AllOk P a) (hb : AllOk P b) : AllOk P (if c then a else b) := by
  split <;> assumption

/-- A rule that writes one destination with a computed value keeps the frame. -/
private theorem allOkO_mapReg {α : Type} {op : Op} {t : TState} {d : Nat} {o : Option α}
    {v : α → Value} (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    AllOkO (LocalFrame op t) (o.map fun a => pure (next (setReg t d (v a)))) := by
  intro e he
  cases o with
  | none => cases he
  | some a =>
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    exact frame_set hpc hd

/-- The `min` and `max` arm of the numerical rule, for any number of extra operands. -/
private theorem allOkO_erealPick {op : Op} {t : TState} {d : Nat} {fmt : FloatFmt}
    {x y : EReal} {mx : Bool} {rest : List Opnd}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    AllOkO (LocalFrame op t)
      (let pick : EReal → EReal → EReal := fun u v => if mx then max u v else min u v
       match rest with
       | [] => some (pure (next (setReg t d (Assumption.erealValue fmt (pick x y)))))
       | [c] => Assumption.bindRead (Assumption.readERealOpnd t fmt c) fun z =>
           some (pure (next (setReg t d (Assumption.erealValue fmt (pick (pick x y) z)))))
       | _ => some (throw .noRule)) := by
  cases rest with
  | nil => exact allOkO_some (frame_set hpc hd)
  | cons c cs =>
    cases cs with
    | nil =>
      apply allOkO_bindRead; intro z
      exact allOkO_some (frame_set hpc hd)
    | cons c' cs' => exact allOkO_some trivial

set_option maxHeartbeats 8000000 in
private theorem execFloat_all {L : Launch} {g : Nat} {t : TState} {op : Op} :
    AllOkO (LocalFrame op t) (Assumption.execIdealFloat L g t op) := by
  cases op with
  | float f =>
    simp only [Assumption.execIdealFloat]
    repeat' first
      | exact allOkO_none
      | (apply allOkO_bindRead; intro v)
      | (refine allOkO_mapReg (hpc := rfl) (hd := by simp_all [writesRegs]))
      | (refine allOkO_erealPick (hpc := rfl) (hd := by simp_all [writesRegs]))
      | (apply allOkO_some; first
          | exact True.intro
          | exact frame_set rfl (by simp_all [writesRegs]))
      | split

  | cvt c =>
    simp only [Assumption.execIdealFloat]
    split
    · apply allOkO_bindRead; intro v
      apply allOkO_some
      exact frame_set rfl (by simp [writesRegs, CvtInstr.widenF16?_d ‹_›])
    · apply allOkO_bindRead; intro v
      apply allOkO_bindRead; intro v'
      apply allOkO_some
      exact frame_set rfl (by simp [writesRegs, CvtInstr.packF16?_d ‹_›])
    · exact allOkO_some trivial
  | _ =>
    simp only [Assumption.execIdealFloat]
    exact allOkO_some trivial

/-- The numerical rule of an assumption writes only the instruction's destination registers. -/
theorem execFloat_frame {L : Launch} {g : Nat} {t t' : TState} {op : Op}
    (h : Assumption.execIdealFloat L g t op = some (.ok t')) :
    LocalFrame op t t' := execFloat_all (.ok t') h

private theorem execInt_all {L : Launch} {g : Nat} {t : TState} {i : IntInstr} :
    AllOk (LocalFrame (.int i) t) (execInt L g t i) := by
  obtain ⟨op, ty, sat, dsts, srcs⟩ := i
  simp only [execInt]
  split
  all_goals repeat first
    | exact True.intro
    | apply frame_set rfl (by simp [writesRegs])
    | apply frame_setCarry rfl (by simp_all [writesRegs])
    | (apply frame_next rfl
       repeat first
         | exact writesOnly_refl
         | apply writesOnly_setReg _ (by simp_all [writesRegs])
         | apply writesOnly_setDst _ (by intro r e; subst e; simp_all [writesRegs]))
    | (apply allOk_bind; intro v)
    | split

theorem execInt_frame {L : Launch} {g : Nat} {t t' : TState} {i : IntInstr}
    (h : execInt L g t i = .ok t') : LocalFrame (.int i) t t' := allOk_get execInt_all h

private theorem execCvt_all {L : Launch} {g : Nat} {t : TState} {c : CvtInstr} :
    AllOk (LocalFrame (.cvt c) t) (execCvt L g t c) := by
  unfold execCvt
  split
  all_goals repeat first
    | exact True.intro
    | apply frame_set rfl (by simp_all [writesRegs])
    | (apply allOk_bind; intro v)
    | (refine allOk_ite ?_ ?_)
    | (refine allOk_cvtInt (hpc := rfl) (hd := by simp_all [writesRegs]))
    | (dsimp only; split)
    | split

theorem execCvt_frame {L : Launch} {g : Nat} {t t' : TState} {c : CvtInstr}
    (h : execCvt L g t c = .ok t') : LocalFrame (.cvt c) t t' := allOk_get execCvt_all h

/-- The core floating rule writes only the instruction's destination registers. -/
private theorem execFloatCore_all {L : Launch} {g : Nat} {t : TState} {f : FloatInstr} :
    AllOk (LocalFrame (.float f) t) (execFloat L g t f) := by
  unfold execFloat
  repeat' first
    | exact True.intro
    | apply frame_set rfl (by simp_all [writesRegs])
    | (apply allOk_mapM_bind; intro v)
    | (apply frame_next rfl
       repeat first
         | exact writesOnly_refl
         | apply writesOnly_setDst _ (by intro r e; subst e; simp_all [writesRegs]))
    | (apply allOk_bind; intro v)
    | (refine allOk_ite ?_ ?_)
    | (dsimp only; split)
    | split

theorem execFloatCore_frame {L : Launch} {g : Nat} {t t' : TState} {f : FloatInstr}
    (h : execFloat L g t f = .ok t') : LocalFrame (.float f) t t' :=
  allOk_get execFloatCore_all h

/-- A parameter-object load changes only its destination registers. -/
private theorem loadParamObject_all {L : Launch} {w dw : Nat} {p : String} {ds : List Nat} :
    ∀ {t : TState} {off : Nat}, AllOk (fun u => u.pc = t.pc ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      u.fault = t.fault ∧ ∀ r, r ∉ ds → u.regs r = t.regs r)
      (loadParamObject L w dw p t off ds) := by
  induction ds with
  | nil => intro t off; exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons d ds ih =>
    intro t off
    simp only [loadParamObject]
    apply allOk_bind; intro x
    have h := ih (t := setReg t d (paramElem w dw x)) (off := off + w / 8)
    revert h
    cases loadParamObject L w dw p (setReg t d (paramElem w dw x)) (off + w / 8) ds
      with
    | error => intro _; trivial
    | ok u =>
      rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, h4, fun r hr => ?_⟩
      rw [h5 r (fun h => hr (List.mem_cons_of_mem _ h))]
      exact Function.update_of_ne (fun h => hr (by subst h; exact List.mem_cons_self)) _ _

/-- Sign extension changes only the registers it extends. -/
private theorem signExtendRegs_frame {w dw : Nat} {ds : List Nat} :
    ∀ {u : TState}, (signExtendRegs w dw u ds).pc = u.pc ∧ (signExtendRegs w dw u ds).sub = u.sub ∧
      (signExtendRegs w dw u ds).acc = u.acc ∧ (signExtendRegs w dw u ds).fault = u.fault ∧
      ∀ r, r ∉ ds → (signExtendRegs w dw u ds).regs r = u.regs r := by
  induction ds with
  | nil => intro u; exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons d ds ih =>
    intro u
    simp only [signExtendRegs]
    split
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih (u := setReg u d ((MemExt.sign dw).extendBits w _))
      refine ⟨h1, h2, h3, h4, fun r hr => ?_⟩
      rw [h5 r (fun h => hr (List.mem_cons_of_mem _ h))]
      exact Function.update_of_ne (fun h => hr (by subst h; exact List.mem_cons_self)) _ _
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih (u := u)
      exact ⟨h1, h2, h3, h4, fun r hr => h5 r (fun h => hr (List.mem_cons_of_mem _ h))⟩

/-- The state after a parameter-object load into the registers of an `ld.param`. -/
private theorem ldParam_frame {a : MemAccess} {t u : TState}
    (h : u.pc = t.pc ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault ∧
      ∀ r, r ∉ a.regs → u.regs r = t.regs r) : LocalFrame (.mem a) t (next u) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨.inl (by simp [next, nextPc, h1]), h2, h3, h4,
    fun r hr => h5 r (by simpa [writesRegs] using hr)⟩

/-- Every extension of an `ld.param` of a parameter object changes only its registers. -/
private theorem ldParamExt_all {L : Launch} {t : TState} {a : MemAccess} {p : String} {off : Nat} :
    AllOk (LocalFrame (.mem a) t) (match a.ext with
      | .sign dw => (fun u => next (signExtendRegs a.elem.width dw u a.regs)) <$>
        loadParamObject L a.elem.width a.elem.width p t off a.regs
      | .zero dw => next <$> loadParamObject L a.elem.width dw p t off a.regs
      | .same => next <$> loadParamObject L a.elem.width a.elem.width p t off a.regs) := by
  split
  · refine allOk_map (loadParamObject_all (L := L) (p := p) (t := t) (off := off)) ?_
    rintro u ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨g1, g2, g3, g4, g5⟩ := signExtendRegs_frame (w := a.elem.width) (dw := ‹_›)
      (ds := a.regs) (u := u)
    exact ldParam_frame ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4,
      fun r hr => (g5 r hr).trans (h5 r hr)⟩
  all_goals
    exact allOk_map (loadParamObject_all (L := L) (p := p) (t := t) (off := off)) fun _ hu =>
      ldParam_frame hu

private theorem execMove_all {L : Launch} {g : Nat} {t : TState} {op : Op} :
    AllOk (LocalFrame op t) (execMove L g t op) := by
  cases op
  all_goals simp only [execMove]
  case mem a =>
    rcases a with ⟨kind, space, sem, scope, elem, vec, ext, nc, noftz, hints, ⟨base, off⟩, dsts,
      srcs, mmio⟩
    cases base
    case param p obj =>
      cases obj
      · simp only
        split
        · split
          · exact frame_set rfl (by simp_all [writesRegs])
          · exact True.intro
        all_goals first | exact True.intro | simp_all
      · exact ldParamExt_all
    case reg r w =>
      apply allOk_bind; intro p
      exact ldParamExt_all
    all_goals exact True.intro
  all_goals repeat first
    | exact True.intro
    | apply frame_set rfl (by simp_all [writesRegs])
    | apply frame_set2 rfl (by simp_all [writesRegs]) (by simp_all [writesRegs])
    | (apply frame_next rfl
       repeat first
         | exact writesOnly_refl
         | apply writesOnly_setDst _ (by intro r e; subst e; simp_all [writesRegs]))
    | (apply allOk_bind; intro v)
    | (split)

theorem execMove_frame {L : Launch} {g : Nat} {t t' : TState} {op : Op}
    (h : execMove L g t op = .ok t') : LocalFrame op t t' := allOk_get execMove_all h

private theorem execSharedAddress_all {L : Launch} {g : Nat} {t : TState} {c : AddrInstr} :
    AllOk (LocalFrame (.addr c) t) (execSharedAddress L g t c) := by
  unfold execSharedAddress
  split
  all_goals repeat first
    | exact True.intro
    | apply frame_set rfl (by simp [writesRegs, Assumption.addrOperands])
    | (apply allOk_bind; intro v)
    | split

theorem execSharedAddress_frame {L : Launch} {g : Nat} {t t' : TState} {c : AddrInstr}
    (h : execSharedAddress L g t c = .ok t') : LocalFrame (.addr c) t t' :=
  allOk_get execSharedAddress_all h

/-- A `cvta` or `isspacep` writes only its destination register. -/
private theorem execCvta_all {L : Launch} {g : Nat} {t : TState} {c : AddrInstr} :
    AllOk (LocalFrame (.addr c) t) (execCvta L g t c) := by
  unfold execCvta
  split
  all_goals repeat first
    | exact True.intro
    | apply frame_set rfl (by simp_all [writesRegs, Assumption.addrOperands])
    | (apply allOk_bind; intro v)
    | split

theorem execCvta_frame {L : Launch} {g : Nat} {t t' : TState} {c : AddrInstr}
    (h : execCvta L g t c = .ok t') : LocalFrame (.addr c) t t' :=
  allOk_get execCvta_all h

/-- A cache policy, `nanosleep` or `pmevent` writes only the policy's destination register. -/
private theorem execMisc_all {L : Launch} {g : Nat} {t : TState} {m : MiscInstr} :
    AllOk (LocalFrame (.misc m) t) (execMisc L g t m) := by
  cases m with
  | createPolicy d k =>
    cases k with
    | range global a primary total =>
      simp only [execMisc, execPolicy]
      repeat' first
        | exact True.intro
        | exact frame_set rfl (by simp [writesRegs])
        | (apply allOk_bind; intro v)
        | split
    | fraction f =>
      simp only [execMisc, execPolicy]
      repeat' first
        | exact True.intro
        | exact frame_set rfl (by simp [writesRegs])
        | (apply allOk_bind; intro v)
        | split
    | cvt a =>
      simp only [execMisc, execPolicy]
      repeat' first
        | exact frame_set rfl (by simp [writesRegs])
        | (apply allOk_bind; intro v)
  | nanosleep o =>
    simp only [execMisc]
    apply allOk_bind; intro v
    exact frame_next_t rfl
  | pmevent mask a => exact frame_next_t rfl
  | gridDep w => exact frame_next_t rfl

theorem execMisc_frame {L : Launch} {g : Nat} {t t' : TState} {m : MiscInstr}
    (h : execMisc L g t m = .ok t') : LocalFrame (.misc m) t t' := allOk_get execMisc_all h

private theorem execTensorMapPrefetch_all {L : Launch} {g : Nat} {t : TState} {op : Op} :
    AllOk (LocalFrame op t) (execTensorMapPrefetch L g t op) := by
  cases op <;> simp only [execTensorMapPrefetch]
  all_goals repeat first
    | exact True.intro
    | exact ⟨.inl rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    | (apply allOk_bind; intro v)
    | split

theorem execTensorMapPrefetch_frame {L : Launch} {g : Nat} {t t' : TState} {op : Op}
    (h : execTensorMapPrefetch L g t op = .ok t') : LocalFrame op t t' :=
  allOk_get execTensorMapPrefetch_all h

private theorem execPrefetch_all {L : Launch} {g : Nat} {t : TState} {c : AddrInstr} :
    AllOk (LocalFrame (.addr c) t) (execPrefetch L g t c) := by
  unfold execPrefetch
  have hn : LocalFrame (.addr c) t (next t) := ⟨.inl rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  split
  · exact hn
  · apply allOk_bind; intro v
    split
    · exact hn
    · trivial
  · trivial

theorem execPrefetch_frame {L : Launch} {g : Nat} {t t' : TState} {c : AddrInstr}
    (h : execPrefetch L g t c = .ok t') : LocalFrame (.addr c) t t' :=
  allOk_get execPrefetch_all h

/-- A branch keeps the frame, at its target or at an entry of its target list. -/
theorem execBranch_frame {L : Launch} {g : Nat} {t t' : TState} {op : Op}
    (h : execBranch L g t op = .ok t') : LocalFrame op t t' := by
  cases op with
  | bra target u =>
    simp only [execBranch] at h
    cases h
    exact ⟨.inl rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | brx index targets u =>
    simp only [execBranch, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · rename_i ht
        cases h
        exact ⟨.inr (List.mem_of_getElem? ht), rfl, rfl, rfl, fun _ _ => rfl⟩
      · cases h
  | _ => simp only [execBranch] at h; cases h

theorem execLocal_frame {L : Launch} {g : Nat} {t t' : TState} {op : Op}
    (h : execLocal L g t op = .ok t') : LocalFrame op t t' := by
  cases op with
  | int i =>
    cases hr : i.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execInt_frame h
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | float f =>
    cases hr : f.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execFloatCore_frame h
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | move m =>
    cases hr : m.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | cvt c =>
    cases hr : c.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execCvt_frame h
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | mem a =>
    cases hr : a.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | addr c =>
    cases hr : c.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execCvta_frame h
        | exact execSharedAddress_frame h
        | exact execPrefetch_frame h
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | misc m =>
    cases m <;> simp only [execLocal, Op.rule, MiscInstr.rule] at h
    all_goals exact execMisc_frame h
  | warp w =>
    cases hr : w.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | matrix m =>
    cases hr : m.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | fence f =>
    cases hr : f.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | tcMma m =>
    cases hr : m.rule with
    | none => simp only [execLocal, Op.rule, hr] at h; cases h
    | some r =>
      cases r <;> simp only [execLocal, Op.rule, hr] at h
      all_goals first
        | exact execMove_frame h
        | exact execTensorMapPrefetch_frame h
        | exact execBranch_frame h
        | (cases h)
  | prefetchTensorMap generic w src =>
    simp only [execLocal, Op.rule] at h
    exact execTensorMapPrefetch_frame h
  | bra target u =>
    simp only [execLocal, Op.rule] at h
    exact execBranch_frame h
  | brx index targets u =>
    simp only [execLocal, Op.rule] at h
    exact execBranch_frame h
  | _ =>
    simp only [execLocal, Op.rule] at h
    first | (cases h)

private theorem approx_all {t : TState} {op : Op} :
    AllOkO (LocalFrame op t) (Assumption.execApproxExact t op) := by
  cases op <;> simp only [Assumption.execApproxExact]
  all_goals repeat first
    | (apply allOkO_some; first
        | exact True.intro
        | apply frame_set rfl (by simp_all [writesRegs]))
    | (apply allOkO_bindRead; intro v)
    | (split)

/-- Every rule an assumption of `A` gives a local operation writes only that operation's
registers. -/
def RulesFrame (A : List Assumption) : Prop :=
  ∀ a ∈ A, ∀ L g t op t', a.localRule L g t op = some (.ok t') → LocalFrame op t t'

theorem idealReal_frame {name why : String} {s : Assumption.IdealScope} {L : Launch} {g : Nat}
    {t t' : TState} {op : Op}
    (h : (Assumption.idealReal name s why).localRule L g t op = some (.ok t')) :
    LocalFrame op t t' := by
  simp only [Assumption.idealReal] at h
  split at h
  · split at h
    · exact execFloat_frame h
    · cases h
  · cases h

theorem approxExact_frame {name why : String} {fs : List Assumption.ApproxForm} {L : Launch}
    {g : Nat} {t t' : TState} {op : Op}
    (h : (Assumption.approxExact name fs why).localRule L g t op = some (.ok t')) :
    LocalFrame op t t' := by
  simp only [Assumption.approxExact] at h
  split at h
  · split at h
    · exact allOkO_get approx_all h
    · cases h
  · cases h

theorem RulesFrame.nil : RulesFrame [] := by simp [RulesFrame]

theorem RulesFrame.idealReal {name why : String} {s : Assumption.IdealScope}
    {A : List Assumption} (h : RulesFrame A) :
    RulesFrame (Assumption.idealReal name s why :: A) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact fun _ _ _ _ _ => idealReal_frame
  · exact h a ha

theorem RulesFrame.approxExact {name why : String} {fs : List Assumption.ApproxForm}
    {A : List Assumption} (h : RulesFrame A) :
    RulesFrame (Assumption.approxExact name fs why :: A) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact fun _ _ _ _ _ => approxExact_frame
  · exact h a ha

theorem execLocalA_frame {A : List Assumption} (hA : RulesFrame A) {L : Launch} {g : Nat}
    {t t' : TState} {op : Op} (h : execLocalA A L g t op = .ok t')
    (hS : Assumption.SegFreePc A t.pc := by seg_free) : LocalFrame op t t' := by
  rw [hS.exec rfl] at h
  unfold execLocalRule at h
  cases hf : A.findSome? (fun a => a.localRule L g t op) with
  | none =>
    simp only [hf] at h
    exact execLocal_frame h
  | some r =>
    simp only [hf] at h
    obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hf
    subst h
    exact hA a ha L g t op t' hr

end
end PTX.Proof
