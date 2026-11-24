-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.Schedule
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputBytes
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputHandoff
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputRegion
public import Kernels.FlashAttn4Fwd.Proof.Result.Final
public import Kernels.FlashAttn4Fwd.Proof.Result.Values
public import Lemmas.Kernel.Goals

@[expose] public section

/-! # `ResultGoal`

This file sits at the top of the proof tree, outside the layer order: it instantiates the result
layer with the protocols' exports. The schedule gives the item coordinates (`itemCoords`). The
output staging ring (`Output.outputHandoff`, `stagingAsync`) gives every byte a tensor store
writes as the byte its slot's row thread last wrote at the slot's staging byte in the store's
item (`staged_byte`). With the values the correction threads stage (`OutputValues`), reduced to
the attention output by `Result.run_attn`, the stores write the attention output
(`store_values`), and the final memory of a complete execution is the specified output
(`result_goal_of`).

`ResultRemaining` holds, per consistent execution, the thread layer's exports this goal still
takes as premises (`ResultInputs`); `OutputValues` is the correction and softmax runs' export. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The thread layer's exports `ResultGoal` takes, for one execution. -/
structure ResultInputs (P : Params) (L : Launch) (X : Execution) : Prop where
  output : OutputFacts L X
  tmem : TmemFacts L X
  rings : RingFacts L X
  /-- Every MMA operand read is in a ring region. -/
  mmaReads : MmaReadsRings L X
  /-- Each output barrier's history starts with its only initialization. -/
  outputInit : Output.OutputInit L X
  /-- A successful wait is in a canonical spin (DEP-CANONICAL-SPIN). -/
  spin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, kernel.CanonicalSpin pc exit
  store : StoreFacts P L X
  writes : WriteFacts L X

/-- The thread layer's exports `ResultGoal` takes, for every consistent execution. -/
def ResultRemaining (P : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X, Consistent L kernel asms mem0 X → ResultInputs P L X

/-- **The schedule's item coordinates.** -/
theorem itemCoords (hpre : Pre P L mem0) : ItemCoords P L :=
  ⟨Schedule.totOf_items hpre, Schedule.clusterCount_eq hpre, fun _ hw =>
    Schedule.coords_eq hpre (by have := hpre.scheduleRange; omega)⟩

/-- The tiles of item `j` depend on a thread only through its CTA. -/
theorem tile_cta {g g' : Nat} (h : ctaOf L g = ctaOf L g') (j st : Nat) :
    tileBatch L g j = tileBatch L g' j ∧ tileHead L g j = tileHead L g' j ∧
      tileRow L g j st = tileRow L g' j st := by
  simp [tileRow, tileBlock, tileHead, tileBatch, workOf, clusterOf, rankOf, h]

/-- **The byte a tensor store writes** at slot `(x, y, z)` of half `hh` of stage `st` of item `j`
is the byte that the slot's row thread wrote last at the slot's staging byte in item `j`. -/
theorem staged_byte (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : OutputFacts L X) (hH : Output.OutputHandoff L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStaging L l →
      ∃ x y k, p = .read (.store x y k))
    (hs : StoreFacts P L X) (htm : TmemFacts L X) {g k pc a j st hh x y z : Nat}
    {o : TensorStore.Observation}
    {b : Byte} (hget : X.get (g, k) = some ⟨pc, .tensorStore a (oSpec P L g j st hh)⟩)
    (harr : arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k) = j) (hst : st < 2)
    (hhh : hh < 2) (hx : x < 64) (hy : y < 128) (hz : z < 2) (ho : X.tensorStores (g, k) = some o)
    (hwb : TensorStore.writeByte o x y z = some b) :
    ∃ n dst bs, Output.gen L X (ctaOf L g) st j
        (Output.rowThread L (stageLoc L (ctaOf L g) st hh x y z), n) ∧
      X.Writes (Output.rowThread L (stageLoc L (ctaOf L g) st hh x y z), n) dst bs ∧
      dst.Covers (stageLoc L (ctaOf L g) st hh x y z) ∧
      some b = wbyte dst bs (stageLoc L (ctaOf L g) st hh x y z) := by
  have hg := event_thread_lt hX hget
  obtain ⟨st', hh', h13, hsrc, -, -, -, hspec⟩ := hs.spec hg hget
  -- the store's stage and half are the specification's
  have hbase := congrArg (fun s : TensorStore.Spec => s.sharedBase.addr) hspec
  simp only [oSpec, stageBase] at hbase
  have hst' : (st' : Nat) = st := by omega
  rw [hst'] at hsrc
  have hl := Result.oSpec_readLoc (P := P) (L := L) (g := g) (j := j) (st := st) (hh := hh) hx hy hz
  have hr : Output.rd L X (ctaOf L g) st j (g, k) (x, y, z) :=
    ⟨⟨hg, rfl, h13⟩, ⟨pc, a, _, hget, hsrc⟩, harr⟩
  obtain ⟨n, dst, bs, hgen, hwr, hso⟩ :=
    Output.item_source hpre hX ht hH hasync hst (hsrc.2.1 x y z _ hl) hr
  have hord := hso (g, k) x y z pc a _ hr hget hl
  have hred : o.spec.reduce = none := by
    obtain ⟨⟨addr', pc', hg'⟩, -⟩ := hX.store (g, k) o ho
    rw [hget] at hg'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at hg'
    rw [← hg'.2.2]
    rfl
  have hspo : o.spec = oSpec P L g j st hh := by
    obtain ⟨⟨addr', pc', hg'⟩, -⟩ := hX.store (g, k) o ho
    rw [hget] at hg'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at hg'
    exact hg'.2.2.symm
  have hwr' : X.Writes (Output.rowThread L (stageLoc L (ctaOf L g) st hh x y z), n) dst bs := by
    rcases hwr with hw | ⟨_, _, hm⟩
    · exact hw
    · exact (htm.no_rmw hm).elim
  exact ⟨n, dst, bs, hgen, hwr', hord.2.1,
    hX.store_read_byte ho hred hwb (by rw [hspo]; exact hl) hord⟩

/-- **The output values**: the bytes the stores write are the attention output, from the values
the correction threads stage (`OutputValues`) and the output staging ring. -/
theorem store_values (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : OutputFacts L X) (hH : Output.OutputHandoff L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStaging L l →
      ∃ x y k, p = .read (.store x y k))
    (hs : StoreFacts P L X) (htm : TmemFacts L X) (hv : OutputValues P L X) :
    StoreValues P L X := by
  intro g k pc a j st hh x y z o b hget harr hst hhh hx hy hz ho hwb
  obtain ⟨n, dst, bs, ⟨⟨hrt, hrc, h8, h12⟩, -, hrj⟩, hwr, hcov, hb⟩ :=
    staged_byte hpre hX ht hH hasync hs htm hget harr hst hhh hx hy hz ho hwb
  have hval := hv.staged hrt h8 h12 hwr hst hhh hx hy hz (by rw [hrc]; exact hcov)
  rw [hrc, hrj] at hval
  obtain ⟨c0, l0, O, hrun, hw⟩ := hval
  obtain ⟨e1, e2, e3⟩ := tile_cta hrc j st
  rw [e1, e2, e3] at hrun
  rw [hw, Result.run_attn hpre.skPos hpre.skDiv128 hrun (by omega)] at hb
  exact Option.some.inj hb

/-- **`ResultGoal`** from the thread layer's exports (`ResultRemaining`) and the values the
correction threads stage (`OutputValues`). -/
theorem result_goal_of (hpre : Pre P L mem0) (hR : ResultRemaining P L mem0)
    (hval : ∀ X, Consistent L kernel asms mem0 X → Complete L X → OutputValues P L X) :
    ResultGoal kernel asms L mem0 (Post P mem0) := fun X _ hX hd hf => by
  have hi := hR X hX
  have hH := Output.outputHandoff hpre hX hi.output hi.tmem hi.outputInit hi.spin
  have hsa := stagingAsync hX hi.rings hi.output hi.tmem hi.mmaReads
  exact Result.post_of hpre (itemCoords hpre) hX hd hi.store hi.writes
    (store_values hpre hX hi.output hH hsa hi.store hi.tmem (hval X hX hd)) hf

end

end PTX.Kernels.FlashAttn4Fwd.Proof
