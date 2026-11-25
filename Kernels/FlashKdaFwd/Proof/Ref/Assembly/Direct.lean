-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.DirectNoUb
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.DirectFoot
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProgressSites

@[expose] public section

/-!
# The direct safety facts and the sources of the tensor loads, for every consistent execution

This file assembles the fourteen fields of `Top.DirectFacts P L mem0 X` (`Proof/Top/Wire.lean`)
and the progress premise `TensorSources L mem0 X` (`Lemmas/Step/TensorDrain.lean`) from the
per-phase theorems of the reference layer (`Proof/Ref`), by the case principle of the chain
(`Assembly.Stage`: every followed state of a thread is in one of seven phases, with that
phase's invariant).

    theorem direct (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
        (hD : DataHalf P L mem0 X) : Top.DirectFacts P L mem0 X
    theorem tensorSources (hpre : Pre P L mem0)
        (hmax : Maximal L kernel Assumptions.all mem0 X) : TensorSources L mem0 X

**Where each field comes from.**

| field | theorem | from |
|---|---|---|
| `computeNoUb`, `loadNoUb`, `storeNoUb` | `Direct.noUb` (`DirectNoUb.lean`) | `DataHalf` |
| `memSpaces`, `sharedFrame` | `Direct.memSpaces`, `Direct.sharedFrame` | `intent_class` |
| `globalReadFrame` | `Direct.globalReadFrame` | `intent_class` |
| `writeFrame` | `Direct.writeFrame` | `intent_class`, `GWrite.frame` |
| `globalWriteOnce` | `Direct.globalWriteOnce` | `intent_class`, `GWrite.unique` |
| `matrixShape` | `Direct.matrixShape` | `matrix_event` |
| `matrixCount` | `Direct.matrixCount` | `matrix_event`, `Epilogue.matrix_exit` |
| `mmaOperands` | field of `DataHalf` | the value layer |
| `loadFill`, `loadBounds` | `Source.loads_fill`, `Source.loads_bounds` | `Direct.loadShapes` |
| `storeBounds` | `Direct.storeBounds` | `memEv` |

Only the three no-undefined-behaviour fields and `mmaOperands` use the data half
`DataHalf` (`DirectData.lean`: what the value layers owe); the ten other fields and
`tensorSources` are proved from the precondition and consistency alone. Nothing else is
assumed: no phase owes anything to this file.

`Direct.tensorSources` is the statement for every consistent execution (a maximal execution is
consistent).

**Words.** `intent_class` (`DirectFoot.lean`) puts every memory operation of the execution
into one of three classes: in the window of the issuing thread's block, a read of launch
input bytes, or a global write (`GWrite`). `memEv` (`DirectMem.lean`) classifies the events.
A *matrix event* is the warp-level event of one of the 182 matrix instructions of the tile
loop; `matrix_event` says that it is made by a compute thread at a state of the Compute phase,
at the instruction that the count of the thread's earlier matrix events names, and that the
count stays below 182 per tile of the thread's sequence.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Progress (siteCls kindCls)

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

namespace Direct

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-! ### Memory: spaces, frames, the uniqueness of global writes -/

/-- **`DirectFacts.memSpaces`**: every memory operation is on shared or on global memory. -/
theorem memSpaces : ∀ e a, X.MemTouches e a →
    a.loc.space = .shared ∨ a.loc.space = .global := by
  rintro r a (⟨w, hi⟩ | ⟨i, bs, -, hnc⟩)
  · rcases intent_class hpre hX hi with h | ⟨h, -⟩ | ⟨-, h⟩
    · exact .inl h.1
    · exact .inr h
    · exact .inr (h.global hpre hX)
  · exact (no_nc hpre hX hnc).elim

/-- **`DirectFacts.sharedFrame`**: every access of shared memory is in the data part of the
window of the issuing thread's own block. -/
theorem sharedFrame : ∀ e a, X.MemTouches e a → a.loc.space = .shared →
    a.loc.cta = e.issuer.1 / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304 := by
  rintro r a (⟨w, hi⟩ | ⟨i, bs, -, hnc⟩) hs
  · rcases intent_class hpre hX hi with h | ⟨h, -⟩ | ⟨-, h⟩
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
    · rw [h] at hs
      cases hs
    · rw [h.global hpre hX] at hs
      cases hs
  · exact (no_nc hpre hX hnc).elim

/-- **`DirectFacts.globalReadFrame`**: a byte of global memory that is read is a launch input
byte. -/
theorem globalReadFrame : ∀ e a l, X.MemTouches e a → ¬ X.Intent e a true → a.Covers l →
    l.space = .global → mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l := by
  rintro r a l (⟨w, hi⟩ | ⟨i, bs, -, hnc⟩) hnw hc hgl
  · rcases intent_class hpre hX hi with h | ⟨-, -, h⟩ | ⟨rfl, -⟩
    · rw [covers_space hc, h.1] at hgl
      cases hgl
    · exact h l hc
    · exact absurd hi hnw
  · exact (no_nc hpre hX hnc).elim

/-- A write intent that covers a global byte is a global write of the kernel. -/
theorem gwrite_of {r : AsyncCopy.Ref} {a : Acc} {l : Loc} (hi : X.Intent r a true)
    (hc : a.Covers l) (hgl : l.space = .global) : GWrite P L X r a := by
  rcases intent_class hpre hX hi with h | ⟨-, h, -⟩ | ⟨-, h⟩
  · rw [covers_space hc, h.1] at hgl
    cases hgl
  · cases h
  · exact h

/-- **`DirectFacts.writeFrame`**: every byte of global memory that some operation writes is an
output byte of a token of the batch or a byte of the final state. -/
theorem writeFrame : ∀ w a l, X.Intent w a true → a.Covers l → l.space = .global →
    P.OutputByte l ∨ P.StateByte l :=
  fun r a l hi hc hgl => (gwrite_of hpre hX hi hc hgl).frame hpre hX hc

/-- **`DirectFacts.globalWriteOnce`**: two write intents that cover one global byte are one
operation. -/
theorem globalWriteOnce : ∀ e f a b l, X.Intent e a true → X.Intent f b true → a.Covers l →
    b.Covers l → l.space = .global → e = f :=
  fun e f a b l hi hi' hc hc' hgl =>
    (gwrite_of hpre hX hi hc hgl).unique hpre hX (gwrite_of hpre hX hi' hc' hgl) hc hc'

/-! ### Tensor copies -/

/-- **Every tensor load of the execution is a load of the initial state or of a tile**: the
hypothesis `LoadShapes` of the source side of the loads (`Ref/Source/Sources.lean`). -/
theorem loadShapes : Source.LoadShapes P L X := by
  rintro ⟨g, k⟩ al sp ⟨pc, he⟩
  have hm := memEv hpre hX he (fun f h => by cases h)
  cases hm with
  | quiet h => exact absurd rfl (h.2.2.1 al sp)
  | load hsh _ _ => exact hsh

/-- **`DirectFacts.storeBounds`**: no tensor store selects an out-of-bounds element. -/
theorem storeBounds : ∀ i address s, X.TensorStoreIssue i address s →
    ¬ TensorHasOob s.descriptor s.origin s.rows := by
  rintro ⟨g, k⟩ al sp ⟨pc, he⟩
  have hg := Frame.lt_of_get hX he
  have hm := memEv hpre hX he (fun f h => by cases h)
  cases hm with
  | quiet h => exact absurd rfl (h.2.2.2 al sp)
  | tile hσ hI =>
    obtain ⟨t, i, rfl, hfull, -⟩ := tile_at hpre hX hg he hσ hI
    have hi := i.isLt
    have htok := Store.tok_le hpre g
    exact storeOut_noOob (by omega) (by omega) (headOf_lt hpre hg)
  | final hE hj => exact Epilogue.ts_bounds hpre hX hg hE hj he

/-! ### The matrix schedule -/

omit hX in
/-- The total of matrix events of a compute thread: 182 per tile of its sequence. -/
theorem matrixTotal_compute (hc : tid g < 128) :
    Top.matrixTotal P L g = 182 * Compute.tilesOf P g := by
  have hb : g % 192 < 128 := hc
  simp only [Top.matrixTotal, Top.tilesOf, Top.seqOf, Compute.tilesOf, seqOf, hpre.block, hb,
    ↓reduceIte]

omit hX in
/-- A thread that is no compute thread has no matrix event to make. -/
theorem matrixTotal_other (hc : 128 ≤ tid g) : Top.matrixTotal P L g = 0 := by
  have hb : ¬ g % 192 < 128 := by
    unfold tid at hc
    omega
  simp only [Top.matrixTotal, hpre.block, hb, ↓reduceIte]

/-- **A matrix event** is made by a compute thread at a state of the Compute phase: at the
matrix instruction of the code whose number is the count of the thread's earlier matrix events
modulo 182, with that instruction's operation; and with it the thread has made at most 182
matrix events per tile of its sequence. -/
theorem matrix_event {k pc : Nat} {op : MatrixOp} {own recv : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .matrix op own recv⟩) :
    tid g < 128 ∧
      Top.matrixSites[((X.tr g).take k).countP isMatrix % 182]? = some (pc, op) ∧
      ((X.tr g).take k).countP isMatrix + 1 ≤ 182 * Compute.tilesOf P g := by
  obtain ⟨s, hσ, hst, -⟩ := event_stage hpre hX he (fun f h => by cases h)
  -- the site is a matrix site, hence an instruction of the compute loop
  have hcls : siteCls s.site = .matrix :=
    matrix_site_ind (sounds hpre) hX he hσ rfl (P := fun site => siteCls site = .matrix)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hpc : 2105 < s.site.pc ∧ s.site.pc ≤ 2944 :=
    matrix_site_ind (sounds hpre) hX he hσ rfl
      (P := fun site => 2105 < site.pc ∧ site.pc ≤ 2944)
      (fun j _ => (by decide +kernel : ∀ j : Fin 44,
        2105 < (Site.matrixLoad j).pc ∧ (Site.matrixLoad j).pc ≤ 2944) j)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨hr, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute hpc.1 hpc.2
  obtain ⟨pos, hR, hled, -⟩ := hI
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hR.site
    rw [hs] at hcls
    cases hcls
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    have hsk : (Compute.skOf n).At s.site := hR.site
    obtain ⟨-, hlt, htab, -⟩ := Compute.mx_tab n hn (by rw [← Compute.cls_at hsk]; exact hcls)
    have hcnt : ((X.tr g).take k).countP isMatrix = 182 * t + Compute.matOf n :=
      congrArg Compute.Led.mats hled
    have ht : t < Compute.tilesOf P g := hR.facts.lt
    refine ⟨hr, ?_, by omega⟩
    rw [hcnt, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    obtain ⟨op', hop'⟩ := Compute.mxPcs_site htab
    obtain ⟨ins', i', hc', hi', rfl⟩ := Compute.matrixSites_op hop'
    rw [← Compute.pc_at hsk] at hc' hop'
    obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    obtain rfl : ins' = ins := Option.some.inj (hc'.symm.trans hc)
    rw [hi'] at hf
    have hf' : Fires s.site.pc (matrixTmpl L g tt i') ⟨pc, .matrix op own recv⟩ o := hf
    have hop : op = i'.op := Compute.matrix_op hf' rfl
    have hpc' : pc = s.site.pc := Frame.event_pc (sounds hpre) hX he hσ
    rw [hop', hpc', hop]

/-- **`DirectFacts.matrixShape`**: the `n`-th warp matrix event of a thread is at the
`n mod 182`-th matrix instruction of the code and has its operation. -/
theorem matrixShape : ∀ g k pc op own recv, X.get (g, k) = some ⟨pc, .matrix op own recv⟩ →
    Top.matrixSites[((X.tr g).take k).countP isMatrix % 182]? = some (pc, op) :=
  fun g k pc op own recv he => (matrix_event hpre hX he).2.1

omit hpre hX in
/-- An event of the class of the matrix events is a matrix event. -/
theorem matrix_of_isMatrix {e : Event} (h : isMatrix e = true) :
    ∃ pc op own recv, e = ⟨pc, .matrix op own recv⟩ := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first
    | exact ⟨_, _, _, _, rfl⟩
    | cases h

/-- A thread that is no compute thread makes no matrix event. -/
theorem no_matrix (hc : 128 ≤ tid g) (es : List Event) (hsub : ∀ e ∈ es, e ∈ X.tr g) :
    es.countP isMatrix = 0 := by
  rw [List.countP_eq_zero]
  intro e hmem hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem (hsub e hmem)
  obtain ⟨pc, op, own, recv, rfl⟩ := matrix_of_isMatrix hm
  have := (matrix_event hpre hX (g := g) (k := k) hk).1
  omega

/-- The matrix events among the first `m` events of a thread are at most its total. -/
theorem matrix_le (g : Nat) : ∀ m, m ≤ (X.tr g).length →
    ((X.tr g).take m).countP isMatrix ≤ Top.matrixTotal P L g := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[m]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.countP_take_succ_ite isMatrix he]
    by_cases hmx : isMatrix e = true
    · obtain ⟨pc, op, own, recv, rfl⟩ := matrix_of_isMatrix hmx
      obtain ⟨hc, -, hle⟩ := matrix_event hpre hX (g := g) (k := m) he
      rw [matrixTotal_compute hpre hc, ite_eq_left hmx]
      exact hle
    · rw [ite_eq_right hmx]
      exact ih (by omega)

/-- **`DirectFacts.matrixCount`**: a thread makes at most `matrixTotal` matrix events, and
exactly that many if it exits. -/
theorem matrixCount : ∀ g, (X.tr g).countP isMatrix ≤ Top.matrixTotal P L g ∧
    ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ →
      (X.tr g).countP isMatrix = Top.matrixTotal P L g := by
  intro g
  refine ⟨?_, fun j pc he => ?_⟩
  · have h := matrix_le hpre hX g (X.tr g).length le_rfl
    rwa [List.take_length] at h
  · have hg := Frame.lt_of_get hX he
    obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
    obtain ⟨-, hpc⟩ := exit_site_pc (sounds hpre) hX he hσ rfl
    obtain ⟨j0, s0, past, hj, -, -⟩ := hst.of_pc_epilogue (by omega) (.inl hub)
    rw [Epilogue.matrix_exit hpre hX hg ⟨s0, past.state, past.into⟩ hj he]
    obtain ⟨j1, s1, -, -, ⟨hr, -, hO, -⟩ | ⟨hr, -⟩ | ⟨hr, -⟩⟩ := past.entry
    · rw [matrixTotal_compute hpre hr]
      exact congrArg Compute.Led.mats hO.2.1
    · have hc : 128 ≤ tid g := ((warp_eq4_iff g).mp hr).1
      rw [matrixTotal_other hpre hc]
      exact no_matrix hpre hX hc _ fun e h => List.mem_of_mem_take h
    · have hc : 128 ≤ tid g := by
        unfold warp at hr
        unfold tid
        omega
      rw [matrixTotal_other hpre hc]
      exact no_matrix hpre hX hc _ fun e h => List.mem_of_mem_take h

end

/-- **The sources of the tensor loads are fixed**, for every consistent execution: every
tensor load is routed to its block, has a valid descriptor and a non-empty box, and every
global byte it reads has a launch value that no write of the execution covers. -/
theorem tensorSources (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) : TensorSources L mem0 X :=
  Source.tensorSources hpre hX (writeFrame hpre hX) (loadShapes hpre hX)

end Direct

/-! ### The two results -/

/-- **The direct safety facts of a consistent execution**, from the data half that the value
layers owe (`DataHalf`): the absence of undefined-behaviour events, the footprints of all
memory operations, the uniqueness of global writes, the schedule of the matrix instructions and
the operands of the tensor copies. -/
theorem direct (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hD : DataHalf P L mem0 X) : Top.DirectFacts P L mem0 X where
  computeNoUb g k pc f _ := Direct.noUb hpre hX hD g k pc f
  loadNoUb g k pc f _ _ := Direct.noUb hpre hX hD g k pc f
  storeNoUb g k pc f _ := Direct.noUb hpre hX hD g k pc f
  memSpaces := Direct.memSpaces hpre hX
  sharedFrame := Direct.sharedFrame hpre hX
  globalReadFrame := Direct.globalReadFrame hpre hX
  writeFrame := Direct.writeFrame hpre hX
  globalWriteOnce := Direct.globalWriteOnce hpre hX
  matrixShape := Direct.matrixShape hpre hX
  matrixCount := Direct.matrixCount hpre hX
  mmaOperands := hD.mmaOperands
  loadFill := Source.loads_fill (Direct.loadShapes hpre hX)
  loadBounds := Source.loads_bounds hpre hX (Direct.loadShapes hpre hX)
  storeBounds := Direct.storeBounds hpre hX

/-- **The progress premise `TensorSources`** for a maximal execution. -/
theorem tensorSources (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X) : TensorSources L mem0 X :=
  Direct.tensorSources hpre hmax.1

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
