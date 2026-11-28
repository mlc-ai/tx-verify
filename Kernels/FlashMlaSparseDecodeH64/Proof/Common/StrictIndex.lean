-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictGlue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictSteps
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.StepQ
public import Lemmas.Flow.StepForQ
public import Lemmas.Flow.StepForQPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound

@[expose] public section

/-! # The index warp's strict window

The strict chain under the tag invariant `QT ixQt` (`Code.strictQ_windowPc`) over the thread
machine, from the head's shuffle that sent a lane to the index warp (word `7`) to any later event:
the head's shuffle is strict under the invariant (`Wg1.stepForQ_hsh7`: the exact walk to pc 2332 and
the index warp's strict parameter prefix `Index.qw_entry`), the index warp's states are strict
(`Index.stepQ_*`) while the machine's invariant `IxInv` holds (`Index.succ_inv`). -/

/-! # The strict step under an invariant of one state, at a dispatch level and in the thread

`Code.roleLoop_inl_stepForQ`, `Code.roleLoop_inr_stepForQ`: the strict step obligation under an
invariant (`Code.StepForQ`) of the dispatcher's state or of a sub-role's state of a
`Code.roleLoop`, as `Common/StrictRole.lean`'s `StepFor`. `wg1_inl_stepForQ`,
`wg1_inr_stepForQ` and `thread_wg1_stepForQ` apply them to warpgroup 1's level and the
thread machine. -/

namespace PTX.Flow
open PTX.Proof

noncomputable section

namespace Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
  {P : Code K A L g} {ι E : Type} {R : ι → Code K A L g} {pcOf : E → Nat}
  {enterOf : P.D → Option E} {sel : E → P.D → Option ι}
  {back : (i : ι) → (R i).D → Option P.D} {Q : TState → Prop} {Wf : Event → Prop}

theorem roleLoop_inl_stepForQ {d : P.D} {e : Event}
    (hP : enterOf d = none → P.StepForQ Q Wf d e)
    (hstub : ∀ d r, enterOf d = some r → P.inv d →
      P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [] ∧ StubSite K (pcOf r) = true)
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init)
    (hinit : ∀ i, back i (R i).init = none) :
    (roleLoop P R pcOf enterOf sel back).StepForQ Q Wf (Sum.inl d) e :=
  loopGlue_inl_stepForQ (fun hx => hP (gatedExit_none.mp hx)) (handoff_gatedAt hstub hrole)
    (fun j => match j with
      | Sum.inl i => hinit i
      | Sum.inr _ => rfl)

theorem roleLoop_inr_stepForQ {i : ι} {d : (R i).D} {e : Event}
    (hR : back i d = none → (R i).StepForQ Q Wf d e)
    (hstub : ∀ d r, enterOf d = some r → P.inv d →
      P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [] ∧ StubSite K (pcOf r) = true)
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init)
    (hback : ∀ i d p t, back i d = some p → (R i).AtD d t → (R i).inv d → P.AtD p t ∧ P.inv p)
    (hinit : ∀ i, back i (R i).init = none) :
    (roleLoop P R pcOf enterOf sel back).StepForQ Q Wf (.inr ⟨Sum.inl i, d⟩) e :=
  loopGlue_inr_stepForQ (i := Sum.inl i) hR (handoff_gatedAt hstub hrole)
    (by
      rintro (i | r) d p t hb hat hinv
      · exact hback i d p t hb hat hinv
      · cases hb)
    (fun j => match j with
      | Sum.inl i => hinit i
      | Sum.inr _ => rfl)

end Code
end
end PTX.Flow

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

theorem wg1_inl_stepForQ {Q : TState → Prop} {Wf : Event → Prop} {s : Wg1.Site} {e : Event}
    (hP : Wg1.exitOf s = none → (wg1HeadCode P L g).StepForQ Q Wf s e) :
    (wg1Code P L g).StepForQ Q Wf (Sum.inl s) e :=
  Code.roleLoop_inl_stepForQ (fun hx => hP (by simpa [wg1Enter] using hx)) wg1_hstub wg1_hrole
    wg1_hinit

theorem wg1_inr_stepForQ {Q : TState → Prop} {Wf : Event → Prop} {i : SubEntry}
    {d : (subFrag P L g i).D} {e : Event}
    (h : subBack P L g i d = none → (subFrag P L g i).StepForQ Q Wf d e) :
    (wg1Code P L g).StepForQ Q Wf (.inr ⟨Sum.inl i, d⟩) e :=
  Code.roleLoop_inr_stepForQ h wg1_hstub wg1_hrole wg1_hback wg1_hinit

/-- **A step of the thread machine at a state of warpgroup 1 under an invariant.** -/
theorem thread_wg1_stepForQ {Q : TState → Prop} {Wf : Event → Prop} {s : (wg1Code P L g).D}
    {n : Cls → Nat} {e : Event} (h : (wg1Code P L g).StepForQ Q Wf s e) :
    (thread P L g).StepForQ Q Wf (.inr ⟨Sum.inl Entry.wg1, s⟩, n) e :=
  Code.counted_stepForQ (Code.glue_inr_stepForQ (i := Sum.inl Entry.wg1) h) n

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Arith32 Index

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The events' well-formedness in the window**: the index warp's (`IxWf`), and the head's
shuffle received the word `7`. -/
def IxWfT (P : Params) (e : Event) : Prop :=
  IxWf P e ∧ ∀ md av bv cv recv ok, e.pc = 1843 → e.kind = .shfl md av bv cv recv ok →
    ∃ x, recv = .bits 32 x ∧ scmpi .eq .b x 7 = true

/-- The head's shuffle state of the thread machine. -/
abbrev hshState (P : Params) (L : Launch) (g : Nat) (n : Cls → Nat) : (thread P L g).D :=
  (.inr ⟨Sum.inl Entry.wg1, .inl Wg1.Site.hsh⟩, n)

/-- A state of the index warp in the thread machine. -/
abbrev idxState (P : Params) (L : Launch) (g : Nat) (d : Index.D) (n : Cls → Nat) :
    (thread P L g).D :=
  (.inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.index, d⟩⟩, n)

/-- **The states of the window**: the head's shuffle of an index lane, and the index warp's states
that satisfy `IxInv`. -/
def IxOk (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Prop :=
  (subOk L g .index = true ∧ ∃ n, σ = hshState P L g n) ∨
    ∃ d n, σ = idxState P L g d n ∧ IxInv P d

theorem stepForQ_mono {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}
    {Q : TState → Prop} {Wf Wf' : Event → Prop} {d : C.D} {e : Event} (h : C.StepForQ Q Wf d e)
    (hw : Wf' e → Wf e) : C.StepForQ Q Wf' d e :=
  fun ins hat hi hc hq hw' hf => h ins hat hi hc hq (hw hw') hf

/-- **The head's shuffle of an index lane is strict under the tag invariant.** -/
theorem thread_hshQ (hp : Pre P L m) (n : Cls → Nat) (e : Event) :
    (thread P L g).StepForQ (QT ixQt) (IxWfT P) (hshState P L g n) e := by
  refine thread_wg1_stepForQ (wg1_inl_stepForQ fun _ => ?_)
  refine Wg1.stepForQ_hsh7 e
    (fun e he hpc md av bv cv recv ok hk => he.2 md av bv cv recv ok hpc hk)
    (fun w hw => ?_) fun x ok hx => ?_
  · intro r tg h
    rw [show w.pc = 1844 from hw, show ixQt 1844 = [] by decide +kernel] at h
    simp at h
  · obtain ⟨n, h⟩ := Wg1.head_index_seg (L := L) (g := g) x ok hx
    refine SegQ.comp (SegQ.of_seg h fun _ _ _ hu => ?_) (qw_entry hp Plain.mk')
    intro r tg hr
    simp [hu.1, ixQt_entry] at hr

/-- **A state of the index warp that satisfies the invariant is strict under the tag invariant.** -/
theorem thread_indexQ (hp : Pre P L m) {d : Index.D} (hi : IxInv P d) (n : Cls → Nat)
    (e : Event) : (thread P L g).StepForQ (QT ixQt) (IxWfT P) (idxState P L g d n) e :=
  thread_wg1_stepForQ (wg1_inr_stepForQ fun _ =>
    stepForQ_mono (Index.stepQ hp d hi e) fun h => h.1)

/-- **Every state of the window steps strictly under the tag invariant.** -/
theorem ixOk_stepQ (hp : Pre P L m) {σ : (thread P L g).D} (hok : IxOk P L g σ) (e : Event) :
    (thread P L g).StepForQ (QT ixQt) (IxWfT P) σ e := by
  rcases hok with ⟨-, n, rfl⟩ | ⟨d, n, rfl, hi⟩
  · exact thread_hshQ hp n e
  · exact thread_indexQ hp hi n e

/-- A step of the thread machine at an index state is the index warp's. -/
theorem thread_next_index {d : Index.D} {n : Cls → Nat} {e : Event} {σ' : (thread P L g).D}
    (h : (thread P L g).next (idxState P L g d n) e = some (some σ')) :
    ∃ d3 n', Index.succ P L g d e = some (some d3) ∧ σ' = idxState P L g d3 n' := by
  obtain ⟨h1, h2⟩ := Code.counted_next_some h
  rw [Code.glue_next_inr] at h1
  change (((Index.code P L g).next d e).map _ ).map _ = _ at h1
  rcases hq : (Index.code P L g).next d e with _ | _ | d3
  · rw [hq] at h1; simp at h1
  · rw [hq] at h1; simp at h1
  · rw [hq] at h1
    refine ⟨d3, σ'.2, hq, Prod.ext ?_ rfl⟩
    simp only [Option.map_some, Option.some.injEq, Code.backEnter] at h1
    have hb : subBack P L g SubEntry.index d3 = none := rfl
    simp only [hb] at h1
    exact h1.symm

/-- **The head's shuffle that received `7` enters the index warp** (when the lane's gate passes). -/
theorem thread_next_hsh7 {n : Cls → Nat} {e : Event} {σ' : (thread P L g).D}
    (hgate : subOk L g .index = true) {md av bv cv x ok}
    (hk : e.kind = .shfl md av bv cv (.bits 32 x) ok) (h7 : scmpi .eq .b x 7 = true)
    (h : (thread P L g).next (hshState P L g n) e = some (some σ')) :
    ∃ n', σ' = idxState P L g (ofC (ixFirst P L g)) n' := by
  obtain ⟨h1, h2⟩ := Code.counted_next_some h
  rw [Code.glue_next_inr] at h1
  dsimp only [wg1Code, Code.roleLoop, Code.loopGlue, wg1HeadCode, Wg1.code] at h1
  simp only [Wg1.succ, hk, Wg1.dispatch, h7, ↓reduceIte, Option.map_some, Option.some.injEq,
    Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, hgate] at h1
  exact ⟨σ'.2, Prod.ext h1.symm rfl⟩

/-- A step of the head's shuffle is one of a shuffle event. -/
theorem thread_next_hsh_kind {n : Cls → Nat} {e : Event} {σ' : (thread P L g).D}
    (h : (thread P L g).next (hshState P L g n) e = some (some σ')) :
    ∃ md av bv cv recv ok, e.kind = .shfl md av bv cv recv ok := by
  obtain ⟨h1, -⟩ := Code.counted_next_some h
  rw [Code.glue_next_inr] at h1
  dsimp only [wg1Code, Code.roleLoop, Code.loopGlue, wg1HeadCode, Wg1.code] at h1
  simp only [Wg1.succ] at h1
  split at h1
  · rename_i md av bv cv recv ok hk
    exact ⟨md, av, bv, cv, recv, ok, hk⟩
  · simp at h1

/-- **The window's states are closed under the machine's steps.** -/
theorem ixOk_next {σ σ' : (thread P L g).D} {e : Event} (hok : IxOk P L g σ) (hw : IxWfT P e)
    (hpc : e.pc = (thread P L g).pc σ) (h : (thread P L g).next σ e = some (some σ')) :
    IxOk P L g σ' := by
  rcases hok with ⟨hgate, n, rfl⟩ | ⟨d, n, rfl, hi⟩
  · obtain ⟨md, av, bv, cv, recv, ok, hk⟩ := thread_next_hsh_kind h
    obtain ⟨x, rfl, h7⟩ := hw.2 md av bv cv recv ok hpc hk
    obtain ⟨n', rfl⟩ := thread_next_hsh7 hgate hk h7 h
    exact .inr ⟨_, n', rfl, ixInv_first P L g⟩
  · obtain ⟨d3, n', hs, rfl⟩ := thread_next_index h
    exact .inr ⟨d3, n', rfl, succ_inv hi hw.1 hpc hs⟩

/-- **The index warp's strict window**: from the head's shuffle of an index lane (the state before
event `k0`) to the state before any later event `k0 + (m' + 1)`, along a run whose events in the
window are well formed, the state is strictly good, satisfies the tag invariant and the
window's invariant, and fires its event. -/
theorem ix_window (hp : Pre P L m) {u : TState} {es : List Event} {o : Option TState}
    (hr : Run kernel Assumptions.all L g u es o) {k0 m' : Nat} {d dk0 dn : (thread P L g).D}
    {e' : Event} (hreach : (thread P L g).toMachineU.Reach (some d) u)
    (hafter : (thread P L g).toMachine.after (some d) (es.take k0) = some (some dk0))
    (hgate : subOk L g .index = true) (hk0 : ∃ n, dk0 = hshState P L g n)
    (hW : ∀ e ∈ (es.drop k0).take (m' + 1), IxWfT P e)
    (hafter2 : (thread P L g).toMachine.after (some dk0) ((es.drop k0).take (m' + 1)) =
      some (some dn))
    (hn : es[k0 + (m' + 1)]? = some e') :
    IxOk P L g dn ∧ ∃ t1 o', (thread P L g).Good (some dn) t1 ∧ QT ixQt t1 ∧
      EStep kernel Assumptions.all L g t1 e' o' := by
  obtain ⟨n, rfl⟩ := hk0
  refine Code.strictQ_windowPc (thread_sound hp) (Ok := IxOk P L g)
    (fun σ e hok => ixOk_stepQ hp hok e) (fun σ e σ' hok hw hpc hn => ixOk_next hok hw hpc hn)
    hr hreach hafter (.inl ⟨hgate, n, rfl⟩) (fun t ht => ?_) hW hafter2 hn
  intro r tg h
  rw [show t.pc = 1843 from ht.1.1, show ixQt 1843 = [] by decide +kernel] at h
  simp at h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
