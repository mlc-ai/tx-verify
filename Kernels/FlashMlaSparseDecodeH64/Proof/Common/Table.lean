-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Lemmas.Kernel.Safety.Roles
public import Lemmas.Kernel.Safety.Table
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TmemAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.RefT

@[expose] public section

/-! # The role table of the thread machine

The reference invariant and the shape table of every state of the thread machine
(`Common/Roles.lean`), by the library's `Code.roleJ` and `Code.roleEv`: the startup's at its
states, the selected warpgroup's at the others, none at a stub.

**The ub guard.** The slots of the roles whose steps are UB-tolerant (or entered by such a step)
hold while the thread has made no undefined behaviour (the global class `.ub`): a fault during a
crossing may fire at any pc, so after it the role's own ledger says nothing.

**Day one: every slot is trivial.** Each role has one invariant slot (`<role>J`) and one shape slot
(`<role>Ev`), both `True`; `shapeOk` holds for them by `trivial`. A role lane replaces its two
slots by its reference invariant and shape table (with its fragment in `Common/Roles.lean`) and
its case of `shapeOk` by its `shape` theorem. Warpgroup 1's slots are over its `Code.roleLoop`
state (head, then sub-role): the warpgroup 1 lane splits them by sub-role, and the MMA, TMA and
index lanes fill their sub-role's part. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch}

/-! ### The slots -/

/-- **Slot `Startup`**: the startup's reference invariant. -/
def startupJ (P : Params) (L : Launch) (g : Nat) : (startupCode P L g).D → (Cls → Nat) → Prop :=
  fun d n => Startup.Ref d (n .mbInit) (n .bar0) ∧ Startup.RefW L g d (n .shfl) ∧
    Startup.RefT d (n .tmem)

/-- **Slot `Startup`**: the startup's shape table (`Startup/Shape.lean`). -/
def startupEv (P : Params) (L : Launch) (g : Nat) : (startupCode P L g).D → Event → Prop :=
  Startup.Ev L g

/-- **Slot `Wg0`**: warpgroup 0's reference invariant (`Wg0/Ref.lean`). -/
def wg0J (P : Params) (L : Launch) (g : Nat) :
    (wg0Code P L g (warpW L g)).D → (Cls → Nat) → Prop :=
  fun d n => (n .ub = 0 → Wg0.Ref P L g d (fun c => n (.wg0 c))) ∧
    (n .ub = 0 → Wg0.TmemAt (warpW L g) d (n .tmem))

/-- **Slot `Wg0`**: warpgroup 0's shape table (`Wg0/Shape.lean`). -/
def wg0Ev (P : Params) (L : Launch) (g : Nat) : (wg0Code P L g (warpW L g)).D → Event → Prop :=
  Wg0.Ev P L g (warpW L g)

/-- **Slot `Dequant`**: warpgroup 2's reference invariant at its counts (`Dequant/Ref.lean`) and
shape table (`Dequant/Shape.lean`). -/
def dequantJ (P : Params) (L : Launch) (g : Nat) :
    (dequantCode P L g (warpW L g)).D → (Cls → Nat) → Prop :=
  fun d n => n .ub = 0 → Dequant.Ref L g d (fun c => n (.dequant c))

def dequantEv (P : Params) (L : Launch) (g : Nat) :
    (dequantCode P L g (warpW L g)).D → Event → Prop :=
  Dequant.Ev L g

/-- **Slot `Mma`**: the MMA warp's reference invariant and shape table. -/
def mmaJ (P : Params) (L : Launch) (g : Nat) : (mmaCode P L g).D → (Cls → Nat) → Prop :=
  fun d n => (n .ub = 0 → Mma.Ref L g d (fun c => n (.mma c))) ∧ Mma.SiteOk P L g d

def mmaEv (P : Params) (L : Launch) (g : Nat) : (mmaCode P L g).D → Event → Prop :=
  Mma.Ev L g

/-- **Slot `Tma`**: the TMA warp's reference invariant and shape table. -/
def tmaJ (P : Params) (L : Launch) (g : Nat) : (tmaCode P L g).D → (Cls → Nat) → Prop :=
  fun d n => (n .ub = 0 → Tma.Ref L g d (fun c => n (.tma c))) ∧ Tma.SiteOk P L g d


def tmaEv (P : Params) (L : Launch) (g : Nat) : (tmaCode P L g).D → Event → Prop :=
  Tma.Ev L g

/-- **Slot `Index`**: the index warp's reference invariant (`Index/Ref.lean`) and shape table
(`Index/Ev.lean`). -/
def indexJ (P : Params) (L : Launch) (g : Nat) : (indexCode P L g).D → (Cls → Nat) → Prop :=
  fun d n => n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))

def indexEv (P : Params) (L : Launch) (g : Nat) : (indexCode P L g).D → Event → Prop :=
  Index.Ev P L g

/-- **Slot `Wg1`** (with the sub-roles `Mma`, `Tma`, `Index` and the idle code): none at a stub
of the dispatch level. -/
def wg1J (P : Params) (L : Launch) (g : Nat) : (wg1Code P L g).D → (Cls → Nat) → Prop
  | .inl s, n => Wg1.HRef L g s (n .shfl)
  | .inr ⟨.inl .mma, d⟩, n => 3 ≤ n .shfl ∧ subOk L g .mma ∧ mmaJ P L g d n ∧
      ∀ s, d.site = .leave s → s = idleFirst P L g
  | .inr ⟨.inl .tma, d⟩, n => 3 ≤ n .shfl ∧ subOk L g .tma ∧ tmaJ P L g d n ∧
      ∀ s, d.site = .leave s → s = idleFirst P L g
  | .inr ⟨.inl .index, d⟩, n => 3 ≤ n .shfl ∧ subOk L g .index ∧ indexJ P L g d n
  | .inr ⟨.inl i, _⟩, n => 3 ≤ n .shfl ∧ subOk L g i
  | .inr ⟨.inr _, _⟩, _ => False

/-- The head's and the idle code's tables (`Wg1/Shape.lean`), the MMA warp's slot, none at a
stub. -/
def wg1Ev (P : Params) (L : Launch) (g : Nat) : (wg1Code P L g).D → Event → Prop
  | .inl s => Wg1.Ev L g s
  | .inr ⟨.inl .idle, s⟩ => Wg1.IEv s
  | .inr ⟨.inl .mma, d⟩ => mmaEv P L g d
  | .inr ⟨.inl .tma, d⟩ => tmaEv P L g d
  | .inr ⟨.inl .index, d⟩ => indexEv P L g d
  | .inr ⟨.inr _, _⟩ => fun _ => False

/-! ### The table -/

/-- The warpgroup of each entry. -/
def Entry.wg : Entry → Nat
  | .wg0 => 0
  | .wg1 => 1
  | .dequant => 2

/-- The reference invariant of each warpgroup's fragment: its slot's, after barrier 0 and the
startup's two shuffles, in the launch's warpgroup (the gate `sel` passed). -/
def fragJ (P : Params) (L : Launch) (g : Nat) :
    (i : Entry) → (frag P L g i).D → (Cls → Nat) → Prop
  | .wg0 => fun d n => 1 ≤ n .bar0 ∧ wg0J P L g d n ∧ 2 ≤ n .shfl ∧ wgOf L g = Entry.wg .wg0
  | .wg1 => fun d n => 1 ≤ n .bar0 ∧ wg1J P L g d n ∧ 2 ≤ n .shfl ∧ wgOf L g = Entry.wg .wg1
  | .dequant => fun d n =>
      1 ≤ n .bar0 ∧ dequantJ P L g d n ∧ 2 ≤ n .shfl ∧ wgOf L g = Entry.wg .dequant

/-- The shape table of each warpgroup's fragment. -/
def fragEv (P : Params) (L : Launch) (g : Nat) : (i : Entry) → (frag P L g i).D → Event → Prop
  | .wg0 => wg0Ev P L g
  | .wg1 => wg1Ev P L g
  | .dequant => dequantEv P L g

/-- **The role table of the thread machine.** -/
def table (P : Params) (L : Launch) : Frame.RoleTable (thread P L) where
  J g := Code.roleJ (P := startupCode P L g) (R := frag P L g) (pcOf := Entry.pc)
    (enterOf := startupEnter P L g) (sel := sel P L g) (cls := cls) (startupJ P L g) (fragJ P L g)
  Ev g := Code.roleEv (P := startupCode P L g) (R := frag P L g) (pcOf := Entry.pc)
    (enterOf := startupEnter P L g) (sel := sel P L g) (cls := cls) (startupEv P L g)
    (fragEv P L g)

/-- The shape obligation of warpgroup 1's fragment. -/
theorem wg1_shape {m : Mem0} (hp : Pre P L m) {g : Nat} (σ : (wg1Code P L g).D) (n : Cls → Nat)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState} (hJ : fragJ P L g .wg1 σ n)
    (hat : (wg1Code P L g).AtD σ t) (hi : (wg1Code P L g).inv σ)
    (hc : kernel.code[(wg1Code P L g).pc σ]? = some ins)
    (hf : Fires ((wg1Code P L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e o) :
    wg1Ev P L g σ e := by
  rcases σ with s | ⟨i | r, d⟩
  · exact Wg1.shape hp hat hi.1 hc hf
  · cases i with
    | idle => exact Wg1.ishape hp hat hi.1 hc hf
    | mma => exact Mma.shape hp hat hi.1 hc hf
    | tma => exact Tma.shape hp hat hi.1 hc hf
    | index => exact Index.shape hp hat hi.1 hc hf
  · obtain ⟨-, hw, -⟩ := hJ
    exact hw.elim

/-- **The hand-back of an MMA lane that lost its election**: a concrete state of the MMA warp's
state at the idle code's first event (`leave (idleFirst P L g)`) is one of the head's idle exit. -/
def MmaLeave (P : Params) (L : Launch) (g : Nat) : Prop :=
  ∀ d t, d.site = Mma.Site.leave (idleFirst P L g) → (Mma.code P L g).AtD d t →
    (Wg1.code P L g).AtD Wg1.Site.idle t

/-- **The hand-back holds**: both states sit at the idle code's first event with its table
(`Mma.facts_leave`). -/
theorem mmaLeave {g : Nat} : MmaLeave P L g := by
  intro d t hs hat
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  subst hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hat
  refine ⟨h1, h2, h3, h4, ?_⟩
  show Holds t.regs (idleEnd P L g (idleFirst P L g))
  rw [← Mma.facts_leave P L g _ l0 l1 neg cnt pha par]
  exact h5

/-- **The hand-back of a TMA lane that lost its election** (as `MmaLeave`). -/
def TmaLeave (P : Params) (L : Launch) (g : Nat) : Prop :=
  ∀ d t, d.site = Tma.Site.leave (idleFirst P L g) → (Tma.code P L g).AtD d t →
    (Wg1.code P L g).AtD Wg1.Site.idle t

/-- **The TMA hand-back holds** (`Tma.facts_leave`). -/
theorem tmaLeave {g : Nat} : TmaLeave P L g := by
  intro d t hs hat
  have hf := Tma.facts_leave P L g d _ hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hat
  cases d
  simp only at hs
  subst hs
  refine ⟨h1, h2, h3, h4, ?_⟩
  show Holds t.regs (idleEnd P L g (idleFirst P L g))
  rw [← hf]
  exact h5

/-- **Every event fired from a state with the invariant has the state's shape.** -/
theorem shapeOk {m : Mem0} (hp : Pre P L m) (S : Nat → Prop) : (table P L).ShapeOk S :=
  ⟨fun g _ => Code.roleThread_shape
    (fun d _ _ _ _ _ _ hat hi _ hc hf => Startup.shape hp hat hi hc hf)
    (fun i d n _ _ _ _ hJ hat hi hc hf => by
      cases i with
      | wg1 => exact wg1_shape hp d n hJ hat hi hc hf
      | wg0 => exact Wg0.shape hp hat hi hc hf
      | dequant => exact Dequant.shape (w := warpW L g) hp hat hi hc hf)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
