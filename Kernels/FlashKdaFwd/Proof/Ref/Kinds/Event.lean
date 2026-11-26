-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Table
public import Kernels.FlashKdaFwd.Proof.Thread.Sound
public import Kernels.FlashKdaFwd.Proof.Protocol.Layout
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The kind of an event gives the kind of the site it was fired at

Part of `Ref/Kinds.lean` (read its header first). Throughout, `e` is the event of thread `g` at
trace position `k` (`he : X.get (g, k) = some e`) and `d` is the state of the thread machine
before it (`hσ : Frame.stateAt (code L) X g k = some (some d)`: a *followed* state); `hC` says
that the machines are sound (`sounds hpre` gives it from the precondition) and `hX` that the
execution is consistent. Tracking (`Frame.Tracked`) is not used.

* `site_fires`: `firedAt e.kind d.site.kind = true` — the one general fact; everything else is
  read off it by the table `firedAt` (`Kinds/Fires.lean`).
* One lemma per kind of event, concluding with the site: `bar_site` (`∃ j, d.site = .bar j`),
  `wait_site`, `arrive_site`, `mbInit_site`, `fenceMbarInit_site`, `tensorIssue_site`,
  `tensorStore_site` (these two also say on which side of `firstStoreCopy` the ordinal is),
  `shfl_site`, `elect_site`, `exit_site`, `fenceProxy_site`, `bulkCommit_site`,
  `bulkWait_site`; and for the kinds fired at several kinds of sites a disjunction and an
  elimination form (`matrix_site`, `matrix_site_ind`, `rd_site`, `rd_site_ind`, `wr_site`,
  `wr_site_ind`): to prove `P d.site`, prove `P` of each kind of site that can fire the event.
* `bar0_event`: at one of the nine `bar.sync 0` the event is exactly `.bar 0 none .sync` (no
  undefined behaviour); `isBarId_bar0` evaluates the class "arrival at barrier `id`" there.
* The other direction, for the tensor copies: `tensorCopy_load_event` (a load site fires no
  tensor store), `tensorCopy_store_event` (a store site fires no tensor load issue).
* Statements in the exact shape of their first consumers: `shfl_sites` (the startup phase's
  `ShflSites`), `bar_site_pc` (a barrier event is fired at a `bar` site, at sub-step 0, at one
  of the nine `bar.sync 0` of `Protocol.bar0Pcs` or at instruction 2913, the named barrier of
  the tile loop), `exit_site_pc` (instruction 3835).

An undefined-behaviour event (`.ub`) can be fired at any site and has no lemma. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {e : Event} {d : D}

/-- The machines of all launched threads are sound under the precondition: the hypothesis `hC`
of this layer, from `Thread.sound`. -/
theorem sounds (hpre : Pre P L mem0) : ∀ g < L.threads, (code L g).Sound :=
  fun _ hg => Thread.sound hpre hg

/-- **The kind of an event is one that the kind of its site can fire.** -/
theorem site_fires (hC : ∀ g < L.threads, (code L g).Sound)
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    firedAt e.kind d.site.kind = true := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  have hsub : t.sub = d.site.sub := hat.2.1
  have hk := site_op d.site hc
  rw [← hsub] at hk
  exact fires_opKind hk hf

/-! ### Sites of a kind -/

theorem site_of_elect {s : Site} (h : s.kind = .elect) : ∃ j, s = .elect j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_shfl {s : Site} (h : s.kind = .shfl) : ∃ j, s = .shfl j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_mbarInit {s : Site} (h : s.kind = .mbarInit) : ∃ j, s = .mbarInit j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_fenceMbarInit {s : Site} (h : s.kind = .fenceMbarInit) :
    ∃ j, s = .fenceMbarInit j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_bar {s : Site} (h : s.kind = .bar) : ∃ j, s = .bar j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_mbarArrive {s : Site} (h : s.kind = .mbarArrive) : ∃ j, s = .mbarArrive j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_tensorCopy {s : Site} (h : s.kind = .tensorCopy) : ∃ j, s = .tensorCopy j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_mbarWait {s : Site} (h : s.kind = .mbarWait) : ∃ j, s = .mbarWait j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_fenceProxy {s : Site} (h : s.kind = .fenceProxy) : ∃ j, s = .fenceProxy j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_bulkCommit {s : Site} (h : s.kind = .bulkCommit) : ∃ j, s = .bulkCommit j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_bulkWait {s : Site} (h : s.kind = .bulkWait) : ∃ j, s = .bulkWait j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

theorem site_of_exit {s : Site} (h : s.kind = .exit) : ∃ j, s = .exit j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

/-- The ten `bar.sync` of the program: the nine `bar.sync 0` (`Protocol.bar0Pcs`) and the named
barrier of the tile loop at instruction 2913 (the site `bar 6`). -/
theorem bar_pc (j : Fin 10) : (Site.bar j).pc ∈ Protocol.bar0Pcs ∨ (Site.bar j).pc = 2913 := by
  revert j
  decide

/-- Whether an instruction is `bar.sync 0`. -/
def isBarSync0 : Op → Bool
  | .barSync (.imm i) _ => i == 0
  | _ => false

/-- **The `bar.sync 0` instructions of the program are those at `Protocol.bar0Pcs`** (one
evaluated scan of the code). -/
theorem pcs_barSync0 : pcsWhere isBarSync0 = Protocol.bar0Pcs := by
  decide +kernel

/-! ### One lemma per kind of event -/

section
variable (hC : ∀ g < L.threads, (code L g).Sound)
  (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get (g, k) = some e)
  (hσ : Frame.stateAt (code L) X g k = some (some d))
include hC hX he hσ

/-- The kind of the site, from the kind of the event: `κ` is the only kind of site that fires
an event of the kind of `e`. -/
theorem kind_of_fired {κ : SiteKind} (h : ∀ κ', firedAt e.kind κ' = true → κ' = κ) :
    d.site.kind = κ :=
  h _ (site_fires hC hX he hσ)

/-- **A barrier event** (`bar.sync`) is fired at a `bar` site. -/
theorem bar_site {id : Nat} {c : Option Nat} {m : BarMode} (hk : e.kind = .bar id c m) :
    ∃ j, d.site = .bar j :=
  site_of_bar (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **A poll** (`mbarrier.try_wait`) is fired at an `mbarWait` site. -/
theorem wait_site {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m p ok acq sc) : ∃ j, d.site = .mbarWait j :=
  site_of_mbarWait (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **An arrival** (`mbarrier.arrive`) is fired at an `mbarArrive` site. -/
theorem arrive_site {m : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope}
    (hk : e.kind = .arrive m tx c rel sc) : ∃ j, d.site = .mbarArrive j :=
  site_of_mbarArrive (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **An mbarrier initialization** is fired at an `mbarInit` site. -/
theorem mbInit_site {m : Loc} {c : Nat} (hk : e.kind = .mbInit m c) :
    ∃ j, d.site = .mbarInit j :=
  site_of_mbarInit (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **The release of mbarrier initializations** (`fence.mbarrier_init`) is fired at a
`fenceMbarInit` site. -/
theorem fenceMbarInit_site (hk : e.kind = .fenceMbarInit) : ∃ j, d.site = .fenceMbarInit j :=
  site_of_fenceMbarInit (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **A shuffle** is fired at a `shfl` site. -/
theorem shfl_site {md : ShflMode} {a v : Value} {b c : Nat} {ok : Bool}
    (hk : e.kind = .shfl md a b c v ok) : ∃ j, d.site = .shfl j :=
  site_of_shfl (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **An election** is fired at an `elect` site. -/
theorem elect_site {mask inst ld : Nat} (hk : e.kind = .elect mask inst ld) :
    ∃ j, d.site = .elect j :=
  site_of_elect (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **The exit** is fired at the `exit` site. -/
theorem exit_site (hk : e.kind = .exit) : ∃ j, d.site = .exit j :=
  site_of_exit (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **A proxy fence** is fired at a `fenceProxy` site. -/
theorem fenceProxy_site {pk : ProxyFence} {sc : Option MbarScope}
    (hk : e.kind = .fenceProxy pk sc) : ∃ j, d.site = .fenceProxy j :=
  site_of_fenceProxy (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **A bulk-group commit** is fired at a `bulkCommit` site. -/
theorem bulkCommit_site (hk : e.kind = .bulkCommit) : ∃ j, d.site = .bulkCommit j :=
  site_of_bulkCommit (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **A bulk-group wait** is fired at a `bulkWait` site. -/
theorem bulkWait_site {md : BulkGroup.WaitMode} {n : Nat} (hk : e.kind = .bulkWait md n) :
    ∃ j, d.site = .bulkWait j :=
  site_of_bulkWait (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)

/-- **A matrix event** is fired at one of the four kinds of matrix sites: prove `P` of each to
have it of the event's site. -/
theorem matrix_site_ind {op : MatrixOp} {own recv : List (Option Byte)}
    (hk : e.kind = .matrix op own recv) {P : Site → Prop}
    (hMx : ∀ j row, P (.matrixLoadMx j row)) (hMma : ∀ j, P (.warpMma j))
    (hMove : ∀ j, P (.matrixMove j)) (hSt : ∀ j, P (.matrixStore j)) : P d.site := by
  have h := site_fires hC hX he hσ
  rw [hk] at h
  cases hs : d.site <;> rw [hs] at h <;> first
    | exact hMx _ _
    | exact hMma _
    | exact hMove _
    | exact hSt _
    | cases h

/-- **A matrix event** is fired at the second event of an `ldmatrix`, at an `mma`, at a
`movmatrix` or at the first event of a `stmatrix`. -/
theorem matrix_site {op : MatrixOp} {own recv : List (Option Byte)}
    (hk : e.kind = .matrix op own recv) :
    (∃ j row, d.site = .matrixLoadMx j row) ∨ (∃ j, d.site = .warpMma j) ∨
      (∃ j, d.site = .matrixMove j) ∨ ∃ j, d.site = .matrixStore j :=
  matrix_site_ind hC hX he hσ hk
    (P := fun s => (∃ j row, s = .matrixLoadMx j row) ∨ (∃ j, s = .warpMma j) ∨
      (∃ j, s = .matrixMove j) ∨ ∃ j, s = .matrixStore j)
    (fun j row => .inl ⟨j, row, rfl⟩) (fun j => .inr (.inl ⟨j, rfl⟩))
    (fun j => .inr (.inr (.inl ⟨j, rfl⟩))) (fun j => .inr (.inr (.inr ⟨j, rfl⟩)))

/-- **A memory read** is fired at a load, at a later element of the vector load or at the first
event of an `ldmatrix`: prove `P` of each to have it of the event's site. -/
theorem rd_site_ind {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs)
    {P : Site → Prop} (hLd : ∀ j, P (.load j)) (hEl1 : ∀ j v0, P (.loadEl1 j v0))
    (hEl2 : ∀ j v0 v1, P (.loadEl2 j v0 v1)) (hEl3 : ∀ j v0 v1 v2, P (.loadEl3 j v0 v1 v2))
    (hMx : ∀ j, P (.matrixLoad j)) : P d.site := by
  have h := site_fires hC hX he hσ
  rw [hk] at h
  cases hs : d.site <;> rw [hs] at h <;> first
    | exact hLd _
    | exact hEl1 _ _
    | exact hEl2 _ _ _
    | exact hEl3 _ _ _ _
    | exact hMx _
    | cases h

/-- **A memory read** is fired at a load, at a later element of the vector load or at the first
event of an `ldmatrix`. -/
theorem rd_site {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) :
    (∃ j, d.site = .load j) ∨ (∃ j v0, d.site = .loadEl1 j v0) ∨
      (∃ j v0 v1, d.site = .loadEl2 j v0 v1) ∨ (∃ j v0 v1 v2, d.site = .loadEl3 j v0 v1 v2) ∨
      ∃ j, d.site = .matrixLoad j :=
  rd_site_ind hC hX he hσ hk
    (P := fun s => (∃ j, s = .load j) ∨ (∃ j v0, s = .loadEl1 j v0) ∨
      (∃ j v0 v1, s = .loadEl2 j v0 v1) ∨ (∃ j v0 v1 v2, s = .loadEl3 j v0 v1 v2) ∨
      ∃ j, s = .matrixLoad j)
    (fun j => .inl ⟨j, rfl⟩) (fun j v0 => .inr (.inl ⟨j, v0, rfl⟩))
    (fun j v0 v1 => .inr (.inr (.inl ⟨j, v0, v1, rfl⟩)))
    (fun j v0 v1 v2 => .inr (.inr (.inr (.inl ⟨j, v0, v1, v2, rfl⟩))))
    (fun j => .inr (.inr (.inr (.inr ⟨j, rfl⟩))))

/-- **A memory write** is fired at a store or at the second event of a `stmatrix`: prove `P`
of each to have it of the event's site. -/
theorem wr_site_ind {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) {P : Site → Prop}
    (hSt : ∀ j, P (.store j)) (hWr : ∀ j row, P (.matrixStoreWr j row)) : P d.site := by
  have h := site_fires hC hX he hσ
  rw [hk] at h
  cases hs : d.site <;> rw [hs] at h <;> first
    | exact hSt _
    | exact hWr _ _
    | cases h

/-- **A memory write** is fired at a store or at the second event of a `stmatrix`. -/
theorem wr_site {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) :
    (∃ j, d.site = .store j) ∨ ∃ j row, d.site = .matrixStoreWr j row :=
  wr_site_ind hC hX he hσ hk
    (P := fun s => (∃ j, s = .store j) ∨ ∃ j row, s = .matrixStoreWr j row)
    (fun j => .inl ⟨j, rfl⟩) (fun j row => .inr ⟨j, row, rfl⟩)

/-! ### Tensor loads and tensor stores -/

/-- **A tensor copy before `firstStoreCopy` fires no tensor store**: its instruction is a load
into shared memory. -/
theorem tensorCopy_load_event {j : Fin 258} (hs : d.site = .tensorCopy j)
    (hj : j.val < firstStoreCopy) (a : Nat) (sp : TensorStore.Spec) :
    e.kind ≠ .tensorStore a sp := by
  intro hk
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  have hc' : kernel.code[(Site.tensorCopy j).pc]? = some ins := by rw [← hs]; exact hc
  have h1 := tensorCopy_load hj hc'
  have h2 := fires_tensorStore_op hf hk
  cases hop : ins.op <;> simp [hop, tensorOp, tensorStoreOp] at h1 h2

/-- **A tensor copy from `firstStoreCopy` on fires no tensor load issue**: its instruction is a
store to global memory. -/
theorem tensorCopy_store_event {j : Fin 258} (hs : d.site = .tensorCopy j)
    (hj : firstStoreCopy ≤ j.val) (a : Nat) (sp : TensorCopy.Spec) :
    e.kind ≠ .tensorIssue a sp := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  have hc' : kernel.code[(Site.tensorCopy j).pc]? = some ins := by rw [← hs]; exact hc
  have h1 := tensorCopy_store hj hc'
  have hop : tensorOp ins.op = false := by
    cases hop : ins.op <;> rw [hop] at h1 <;> first | rfl | cases h1
  exact fires_notTensor (eventTmpl_notTensor hop) hf a sp

/-- **A tensor load issue** is fired at a tensor copy before `firstStoreCopy`. -/
theorem tensorIssue_site {a : Nat} {sp : TensorCopy.Spec} (hk : e.kind = .tensorIssue a sp) :
    ∃ j : Fin 258, d.site = .tensorCopy j ∧ j.val < firstStoreCopy := by
  obtain ⟨j, hs⟩ := site_of_tensorCopy (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)
  refine ⟨j, hs, ?_⟩
  by_contra hj
  exact tensorCopy_store_event hC hX he hσ hs (by omega) a sp hk

/-- **A tensor store** is fired at a tensor copy from `firstStoreCopy` on. -/
theorem tensorStore_site {a : Nat} {sp : TensorStore.Spec} (hk : e.kind = .tensorStore a sp) :
    ∃ j : Fin 258, d.site = .tensorCopy j ∧ firstStoreCopy ≤ j.val := by
  obtain ⟨j, hs⟩ := site_of_tensorCopy (kind_of_fired hC hX he hσ fun κ h => by
    rw [hk] at h; cases κ <;> first | rfl | cases h)
  refine ⟨j, hs, ?_⟩
  by_contra hj
  exact tensorCopy_load_event hC hX he hσ hs (by omega) a sp hk

/-! ### Program counters of the barrier and exit sites -/

/-- **At one of the nine `bar.sync 0` the event is the arrival at barrier 0** with no thread
count, and never undefined behaviour: the barrier is an immediate operand. (The tenth barrier,
at instruction 2913, takes its barrier and its count from registers: its event is a matter of
the phase's invariant.) -/
theorem bar0_event (hpc : d.site.pc ∈ Protocol.bar0Pcs) :
    e = ⟨d.site.pc, .bar 0 none .sync⟩ := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  rw [← pcs_barSync0] at hpc
  obtain ⟨ins', hc', hq⟩ := mem_pcsWhere.mp hpc
  have hc0 : kernel.code[d.site.pc]? = some ins := hc
  obtain rfl : ins' = ins := Option.some.inj (hc'.symm.trans hc0)
  have hf0 : Fires d.site.pc (eventTmpl Assumptions.all L g t ins'.op) e o := hf
  cases hop : ins'.op <;> rw [hop] at hq hf0 <;> try cases hq
  rename_i a al
  cases a <;> try cases hq
  rename_i i
  obtain rfl : i = 0 := by simpa [isBarSync0] using hq
  exact shape_barSync (id := 0) (P := fun e' => e' = ⟨d.site.pc, .bar 0 none .sync⟩) hf0
    (by decide) rfl

/-- At a `bar.sync 0` the event is an arrival at barrier `id` exactly when `id = 0`. -/
theorem isBarId_bar0 (hpc : d.site.pc ∈ Protocol.bar0Pcs) (id : Nat) :
    Execution.isBarId id e = (0 == id) := by
  rw [bar0_event hC hX he hσ hpc]
  rfl

/-- **A barrier event is fired at a `bar` site, at sub-step 0, at one of the nine `bar.sync 0`
or at instruction 2913** (the named barrier of the tile loop). -/
theorem bar_site_pc {id : Nat} {c : Option Nat} {m : BarMode} (hk : e.kind = .bar id c m) :
    (∃ j, d.site = .bar j) ∧ d.site.sub = 0 ∧
      (d.site.pc ∈ Protocol.bar0Pcs ∨ d.site.pc = 2913) := by
  obtain ⟨j, hs⟩ := bar_site hC hX he hσ hk
  rw [hs]
  exact ⟨⟨j, rfl⟩, rfl, bar_pc j⟩

/-- **The exit is fired at the `exit` site, instruction 3835.** -/
theorem exit_site_pc (hk : e.kind = .exit) : d.site = .exit 0 ∧ d.site.pc = 3835 := by
  obtain ⟨j, hs⟩ := exit_site hC hX he hσ hk
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [hs]
  exact ⟨rfl, rfl⟩

end

/-! ### In the shape of the first consumers -/

/-- **An event of kind shuffle is fired only at a shuffle site**: the statement `ShflSites L X`
of `Ref/Startup/Shfl.lean`, under the precondition. -/
theorem shfl_sites (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ g k s pc md a b c v ok, g < L.threads →
      Frame.stateAt (code L) X g k = some (some s) →
      X.get (g, k) = some ⟨pc, .shfl md a b c v ok⟩ → ∃ j, s.site = .shfl j :=
  fun _ _ _ _ _ _ _ _ _ _ _ hσ he => shfl_site (sounds hpre) hX he hσ rfl

end PTX.Kernels.FlashKdaFwd.Proof.Ref
