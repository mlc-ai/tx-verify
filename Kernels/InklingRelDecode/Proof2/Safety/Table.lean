-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Ref.BaseRead
public import Kernels.InklingRelDecode.Proof2.Ref.Worker
public import Kernels.InklingRelDecode.Proof2.ProA.Shape
public import Kernels.InklingRelDecode.Proof.Thread.EvSShape
public import Kernels.InklingRelDecode.Proof.Thread.EvDEpi
public import Lemmas.Kernel.Safety.Table
public import Lemmas.Flow.Final

@[expose] public section

/-! # The role table of Inkling

The safety layer's table (`Lemmas/Kernel/Safety/Table.lean`) over the thread machine
(`Common/Roles.lean`):

* `J` is the reference invariant `Ref` the thread machine is followed with (`good_all`);
* `Ev` at a state is the events the instruction at its site fires from a concrete state of the
  state (`InsEv`, by definition), each of which either ends the thread (`Ends`: undefined
  behaviour or the exit) or has the shape of its fragment's table (`FragEv`):

  | States | Shape table |
  |---|---|
  | startup | `Startup.Ev` |
  | prologue | `ProA.Ev` |
  | softmax region | the first tree's `Sm.Shape` |
  | epilogue | the first tree's `Epi.Shape` |
  | loader | the first tree's `EvW.LdShapeW` |
  | MMA warp | the first tree's `EvW.MmShape` |
  | dispatch, idle role, exit path, stubs | the instruction's events only |

`shapeOk` proves the shape obligation for every launched thread: an ending event is an ending
event (`fires_none_ends`), and a continuing event has its fragment's shape by the fragment's shape
theorem. With `good_all'` the table follows every launched thread (`followed`, no premise), so
every frame of `Lemmas/Kernel/Safety/Classes.lean` and every source over a role table applies to
Inkling. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The events the instruction at a state's site fires from a concrete state of the state. -/
def InsEv (C : Flow.Code kernel Assumptions.all L g) (d : C.D) (e : Event) : Prop :=
  ∃ t ins o, C.AtD d t ∧ kernel.code[C.pc d]? = some ins ∧
    Fires (C.pc d) (eventTmpl Assumptions.all L g t ins.op) e o

/-- **The fragments' shape tables** at the thread machine's states. -/
def FragEv (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Event → Prop
  | (.inl s, _), e => Startup.Ev L g s e
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _), e => ProA.Ev L g d e
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .sm d⟩⟩, _), e => Proof.Sm.Shape L g d e
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _), e => Proof.Epi.Shape L g d e
  | (.inr ⟨.inl (.worker _), .loader d _⟩, _), e => Proof.EvW.LdShapeW Q L g d e
  | (.inr ⟨.inl (.worker _), .mma d _⟩, _), e => Proof.EvW.MmShape L g d e
  | _, _ => True

/-- **The role table**: the reference invariant and, per state, the instruction's events, each an
ending event or of the fragment's shape. -/
def table (Q : Params) (L : Launch) : RoleTable (thread Q L) where
  J g := Ref Q L g
  Ev g d e := InsEv (thread Q L g) d e ∧ (Ends e ∨ FragEv Q L g d e)

/-- The launched threads. -/
def Launched (L : Launch) (g : Nat) : Prop := g < L.threads

/-- A continuing event is no undefined behaviour. -/
theorem not_ub_of_some {pc : Nat} {mt : Tmpl} {e : Event} {u : TState}
    (hf : Fires pc mt e (some u)) : ∀ f, e.kind ≠ .ub f := fun f hk => by
  have := fires_end_none hf (.inl ⟨f, hk⟩)
  cases this

/-- The prologue's exit state is not inside the glue's invariant. -/
theorem proA_site_ne {d : ProA.D} (h : ProA.exitOf d = none) : d.site ≠ .exit := by
  intro hs
  simp [ProA.exitOf, hs] at h

/-- **A continuing event has its fragment's shape.** -/
theorem frag_ev (hp : Pre Q L m) (hg : g < L.threads) {d : (thread Q L g).D} {t u : TState}
    {ins : Instr} {e : Event} (hJ : Ref Q L g d) (hat : (thread Q L g).AtD d t)
    (hi : (thread Q L g).inv d) (hc : kernel.code[(thread Q L g).pc d]? = some ins)
    (hf : Fires ((thread Q L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e (some u)) :
    FragEv Q L g d e := by
  obtain ⟨x, n⟩ := d
  rcases x with s | ⟨_ | r, d⟩
  · exact Startup.shape hp hat hi.1 hc hf (not_ub_of_some hf)
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact ProA.shape (Startup.inh L g Q tm) (proA_site_ne (Code.gatedExit_none.mp hi.2))
          hat hi.1 hc hf
      · cases τ with
        | sm d =>
          refine Proof.Sm.shape (u := u) (by rw [hp.block]) (Proof.Sm.sharedOk_of_pre hp)
            ⟨t, hat, hi, ?_⟩
          change Fires t.pc (match kernel.code[d.site.pc]? with
            | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e _
          have hc' : kernel.code[d.site.pc]? = some ins := hc
          rw [hc', hat.1]
          exact hf
        | epi d =>
          refine Proof.Epi.shape (u := u) (by rw [hp.block]) ⟨t, hat, hi.1, ?_⟩
          change Fires t.pc (match kernel.code[d.site.pc]? with
            | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e _
          have hc' : kernel.code[d.site.pc]? = some ins := hc
          rw [hc', hat.1]
          exact hf
      · trivial
    | worker tm =>
      cases d with
      | loader d P =>
        refine Proof.EvW.loader_shapeW (u := u) (P := P) hp hJ.2.2.2 ⟨t, ⟨hat, hi⟩, ?_⟩
        have hc' : kernel.code[(Proof.WComp.code L g Q).pc (.loader d P)]? = some ins := hc
        show Fires t.pc ((Proof.WComp.code L g Q).tmpl (some (.loader d P)) t) e (some u)
        simp only [Code.tmpl]
        rw [hc', hat.1]
        exact hf
      | mma d P =>
        refine Proof.EvW.mma_shape (u := u) hp hg ⟨t, ⟨hat, hi⟩, ?_⟩
        have hc' : kernel.code[(Proof.WComp.code L g Q).pc (.mma d P)]? = some ins := hc
        show Fires t.pc ((Proof.WComp.code L g Q).tmpl (some (.mma d P)) t) e (some u)
        simp only [Code.tmpl]
        rw [hc', hat.1]
        exact hf
      | _ => trivial
  · trivial

/-- **The shape obligation of the role table** for every launched thread. -/
theorem shapeOk (hp : Pre Q L m) : (table Q L).ShapeOk (Launched L) where
  shape g hg d t ins e o hJ hat hi hc hf := by
    refine ⟨⟨t, ins, o, hat, hc, hf⟩, ?_⟩
    cases o with
    | none => exact .inl (fires_none_ends hf)
    | some u => exact .inr (frag_ev hp hg hJ hat hi hc hf)

/-- **The role table follows every launched thread** (`good_all'`). -/
theorem followed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    (table Q L).Followed X (Launched L) :=
  fun _ hg k => good_all' hp hX hg k

end
end PTX.Kernels.InklingRelDecode.Proof2
