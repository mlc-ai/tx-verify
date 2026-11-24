-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Common.FollowView
public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.EvR
public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Softmax.EvS
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Lemmas.Flow.Step.Alloc
public import Lemmas.Kernel.Safety.Table
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.CorrWarp.ControlRead
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Shape
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Shape
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Kernels.TmlFa4Fwd.Proof.Loader.ShapeAll

public import Lemmas.Kernel.Safety.TableU
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics

@[expose] public section

/-! # The role table of the thread machine

`table p L` is the library's role table (`Frame.RoleTable`) of the glued thread machine: its
invariant is every lane's reference invariant (`JR`: the softmax warps' below warp 8, `RefAll`
above), and its shape table at a state is the shape table of the state's fragment: the startup's,
the output warp's, the MMA warp's allocation prefix (`PreEv`) and role, the correction warps'
(both of their tables), the loader warps', the softmax warps' without undefined behaviour, and
nothing at a stub. `table_shape` is the shape obligation for every thread (each fragment's
`Shape`), `table_followed` the following of every thread (`goodR`), so the library's per-class
skeletons (`RoleTable.forall_kind`, `RoleTable.noMbarUninit_of_handoff`, …) apply to every
thread of the launch. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The events of the MMA warp's allocation prefix: its `setmaxnreg`, the allocation request,
the store of the allocated column, or undefined behaviour. -/
def Mma.PreEv (e : Event) : Prop :=
  (∃ inc n inst, e.kind = .setMaxReg inc n inst) ∨
    (∃ grp dst act, e.kind = .tc (.resource grp dst act)) ∨
    (∃ a bs, e.kind = .wr a bs) ∨ ∃ f, e.kind = .ub f

/-- The shape table of a state of the thread machine: its fragment's. -/
def TEv (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Event → Prop
  | (.inl s, _) => Startup.Ev L g s
  | (.inr ⟨.epilogue, d⟩, _) => Epilogue.Ev p L g d
  | (.inr ⟨.mma, .inl _⟩, _) => Mma.PreEv
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => Mma.Ev p L g d
  | (.inr ⟨.correction, d⟩, _) => fun e => Correction.Control.Ev p L g d e ∧ CorrWarp.EvR p L g d e
  | (.inr ⟨.loader b, d⟩, _) => Loader.Ev p L g (Loader.wOf b) d
  | (.inr ⟨.softmax, d⟩, _) => Softmax.EvS p L g d
  | (.inr ⟨.stub _, _⟩, _) => fun _ => True

/-- **The role table of the thread machine.** -/
def table (p : Params) (L : Launch) : Frame.RoleTable (thread p L) where
  J := JR p L
  Ev := TEv p L

/-- The MMA warp's allocation prefix has its shape table. -/
theorem Mma.pre_shape {s : Mma.Start} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hi : (Mma.S p L g (Mma.ent p L)).inv s ∧ Mma.Start.exit s = none)
    (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Assumptions.all L g t ins.op) e o) : Mma.PreEv e := by
  have key : ∀ tm : Tmpl, (AllocT tm ∨ ∃ inc n, tm = SetMaxNReg.tmpl t inc n) →
      Fires s.pc tm e o → Mma.PreEv e := by
    intro tm htm hf
    rcases htm with htm | ⟨inc, n, rfl⟩
    · cases tm with
      | ub f =>
        simp only [Fires] at hf
        obtain ⟨rfl, -⟩ := hf
        exact .inr (.inr (.inr ⟨f, rfl⟩))
      | tc k u =>
        cases k <;> simp only [AllocT] at htm
        simp only [Fires] at hf
        obtain ⟨rfl, -⟩ := hf
        exact .inr (.inl ⟨_, _, _, rfl⟩)
      | tcAllocStore dst u =>
        simp only [Fires] at hf
        obtain ⟨_, -, rfl, -⟩ := hf
        exact .inr (.inr (.inl ⟨_, _, rfl⟩))
      | _ => exact htm.elim
    · simp only [SetMaxNReg.tmpl] at hf
      split at hf <;> simp only [Fires] at hf
      · obtain ⟨_, rfl, -⟩ := hf
        exact .inl ⟨_, _, _, rfl⟩
      · obtain ⟨rfl, -⟩ := hf
        exact .inr (.inr (.inr ⟨_, rfl⟩))
  cases s with
  | set =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1907)
    exact key _ (.inr ⟨_, _, rfl⟩) hf
  | alloc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1909)
    exact key _ (.inl allocT) hf
  | wr =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1909)
    exact key _ (.inl allocT) hf
  | enter => exact absurd hi.2 (by simp [Mma.Start.exit])

/-- **The shape obligation of the role table, for every thread.** -/
theorem table_shape (hp : Pre p L m) :
    (table p L).ShapeOkU (fun g => g < L.threads) := by
  refine ⟨fun g _ σ t ins e o _ hat hi hc hf hu => ?_⟩
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · exact Startup.shape hp hat hi.1 hc hf
  cases i with
  | epilogue => exact Epilogue.shape hp hat hi hc hf
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · exact Mma.pre_shape hi hc hf
    · exact Mma.shape hp hat hi hc hf
  | correction => exact ⟨Correction.Control.shapeAt hp d hat hi hc hf hu,
      Correction.Control.read_shapeAt hp d hat hi hc hf⟩
  | loader b => exact Loader.shape hp hat hi hc hf
  | softmax => exact ⟨Softmax.Control.shapeAt hp d hat hi.1 hc hf, hu⟩
  | stub r => trivial

/-- The role table supplies a shape for every nonfaulting event. -/
theorem table_shapeU (hp : Pre p L m) : (table p L).ShapeOkU (fun g => g < L.threads) :=
  table_shape hp

/-- `table_shape` from the following premises. -/
theorem table_shape_of (hp : Pre p L m) (_hFw : Follow p L X) :
    (table p L).ShapeOkU (fun g => g < L.threads) :=
  table_shape hp

/-- **Every thread is followed with the table's invariant.** -/
theorem table_followed (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    (table p L).Followed X (fun g => g < L.threads) :=
  fun _ hg k => goodR hp hX hFw hg k

end
end PTX.Kernels.TmlFa4Fwd.Proof
