-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Fires
public import Kernels.FlashKdaFwd.Proof.Thread.Sites
public import Kernels.FlashKdaFwd.Spec
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # The kind of the instruction at each site (one evaluated scan of the program)

The table half of `Ref/Kinds.lean` (read its header first). A site of the thread machine is
named by a kind and an ordinal (`Site.bar j` is the `j`-th `bar.sync` of the program); the
program counter of a site (`Site.pc`) is an entry of a generated list. This file proves that
the instruction at that program counter is of the site's kind:

    theorem site_kind (s : Site) : kindAt s.sub s.pc = some s.kind

where `kindAt sub pc` is `opKind sub` (`Kinds/Fires.lean`) of the instruction `kernel.code[pc]`,
and `s.sub` is the sub-step of the site (`Site.sub`: 1 at the second event of an `ldmatrix` or
`stmatrix`, `k` at element `k` of the vector load). `site_op` is the same for a given
instruction.

**How it is checked.** One pass over the 3,836 decoded instructions lists the event
instructions with their kinds (`scanAll`). The theorem `scan`, evaluated by the kernel
(`decide +kernel`), says that for each of the 24 kinds the instructions of the kind (`pcsOf κ`)
are at the program counters of the kind's sites, in order
(`sitePcs κ`, e.g. `(List.finRange 10).map fun j => (Site.bar j).pc`). So the sites of a kind
are exactly the instructions of the kind (`pcsOf_eq`); `site_kind` uses one direction. The
second events and the later elements of the vector load are at sub-steps other than 0; their
kind follows from the kind at sub-step 0 (`opKind_matrixLoad`, `opKind_matrixStore`,
`opKind_load`), without another scan.

**Cost** (measured, one core): `scan` checks in about 6 s (the file in 11 s with the two scans
of the tensor copies; peak memory 3.5 GB). The alternatives were slower: one
scan per kind, 23 scans of about 1 s each (27 s for the file); a lookup `kernel.code[pc]?` per
site (`∀ j : Fin 258, kindAt 0 (Site.tensorCopy j).pc = some .tensorCopy` by `decide +kernel`),
10 s for the 178 loads and 40 s for the 258 tensor copies alone, because each lookup walks the
list of instructions. In the single scan the kernel evaluates the pass once and reuses it for
every kind.

**Tensor copies.** The sites `tensorCopy j` are the loads into shared memory for
`j < firstStoreCopy` (226 of them) and the stores to global memory from there on (32). Two
more scans, `pcs_tensorLoad` and `pcs_tensorStore`, give the instruction class of each
(`tensorCopy_load`, `tensorCopy_store`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof
open PTX PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

/-- **The kind of a site**: its constructor. -/
def Thread.Site.kind : Site → SiteKind
  | .elect _ => .elect
  | .shfl _ => .shfl
  | .mbarInit _ => .mbarInit
  | .fenceMbarInit _ => .fenceMbarInit
  | .bar _ => .bar
  | .load _ => .load
  | .mbarArrive _ => .mbarArrive
  | .tensorCopy _ => .tensorCopy
  | .mbarWait _ => .mbarWait
  | .fenceProxy _ => .fenceProxy
  | .store _ => .store
  | .trap _ => .trap
  | .matrixLoad _ => .matrixLoad
  | .warpMma _ => .warpMma
  | .matrixMove _ => .matrixMove
  | .matrixStore _ => .matrixStore
  | .bulkCommit _ => .bulkCommit
  | .bulkWait _ => .bulkWait
  | .exit _ => .exit
  | .matrixLoadMx _ _ => .matrixLoadMx
  | .matrixStoreWr _ _ => .matrixStoreWr
  | .loadEl1 _ _ => .loadEl1
  | .loadEl2 _ _ _ => .loadEl2
  | .loadEl3 _ _ _ _ => .loadEl3

namespace Ref

/-- The site kind of the instruction at index `pc` when it is at sub-step `sub`. -/
def kindAt (sub pc : Nat) : Option SiteKind :=
  (kernel.code[pc]?).bind fun ins => opKind sub ins.op

/-- The indices of the instructions whose operation satisfies `q`, in program order. -/
def pcsWhere (q : Op → Bool) : List Nat :=
  (kernel.code.zipIdx.filter fun p => q p.1.op).map (·.2)

theorem mem_pcsWhere {q : Op → Bool} {pc : Nat} :
    pc ∈ pcsWhere q ↔ ∃ ins, kernel.code[pc]? = some ins ∧ q ins.op = true := by
  unfold pcsWhere
  simp only [List.mem_map, List.mem_filter, Prod.exists]
  constructor
  · rintro ⟨ins, i, ⟨hm, hq⟩, rfl⟩
    exact ⟨ins, List.mem_zipIdx_iff_getElem?.mp hm, hq⟩
  · rintro ⟨ins, hc, hq⟩
    exact ⟨ins, pc, ⟨List.mem_zipIdx_iff_getElem?.mpr hc, hq⟩, rfl⟩

/-! ### The scan -/

/-- **The event instructions of the program**, each with its kind (at sub-step 0) and its
index, in program order: one pass over the decoded instructions. -/
def scanAll : List (SiteKind × Nat) :=
  kernel.code.zipIdx.filterMap fun p => (opKind 0 p.1.op).map (·, p.2)

/-- The indices of the instructions of kind `κ`, in program order. -/
def pcsOf (κ : SiteKind) : List Nat := (scanAll.filter fun q => q.1 == κ).map (·.2)

theorem mem_pcsOf {κ : SiteKind} {pc : Nat} : pc ∈ pcsOf κ ↔ kindAt 0 pc = some κ := by
  unfold pcsOf scanAll kindAt
  simp only [List.mem_map, List.mem_filter, List.mem_filterMap, Prod.exists, Option.map_eq_some_iff,
    Prod.mk.injEq, beq_iff_eq, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨κ', pc', ⟨⟨ins, i, hm, κ'', hk, rfl, rfl⟩, rfl⟩, rfl⟩
    exact ⟨ins, List.mem_zipIdx_iff_getElem?.mp hm, hk⟩
  · rintro ⟨ins, hc, hk⟩
    exact ⟨κ, pc, ⟨⟨ins, pc, List.mem_zipIdx_iff_getElem?.mpr hc, κ, hk, rfl, rfl⟩, rfl⟩, rfl⟩

/-- **The program counters of the sites of a kind**, by the generated `Site.pc`, in the order
of the ordinals. The second events of the matrix loads and stores and the later elements of the
vector load are at sub-steps other than 0 and have no entry. -/
def sitePcs : SiteKind → List Nat
  | .elect => (List.finRange 5).map fun j => (Site.elect j).pc
  | .shfl => (List.finRange 3).map fun j => (Site.shfl j).pc
  | .mbarInit => (List.finRange 11).map fun j => (Site.mbarInit j).pc
  | .fenceMbarInit => (List.finRange 3).map fun j => (Site.fenceMbarInit j).pc
  | .bar => (List.finRange 10).map fun j => (Site.bar j).pc
  | .load => (List.finRange 178).map fun j => (Site.load j).pc
  | .mbarArrive => (List.finRange 7).map fun j => (Site.mbarArrive j).pc
  | .tensorCopy => (List.finRange 258).map fun j => (Site.tensorCopy j).pc
  | .mbarWait => (List.finRange 10).map fun j => (Site.mbarWait j).pc
  | .fenceProxy => (List.finRange 4).map fun j => (Site.fenceProxy j).pc
  | .store => (List.finRange 146).map fun j => (Site.store j).pc
  | .trap => (List.finRange 14).map fun j => (Site.trap j).pc
  | .matrixLoad => (List.finRange 44).map fun j => (Site.matrixLoad j).pc
  | .warpMma => (List.finRange 104).map fun j => (Site.warpMma j).pc
  | .matrixMove => (List.finRange 16).map fun j => (Site.matrixMove j).pc
  | .matrixStore => (List.finRange 18).map fun j => (Site.matrixStore j).pc
  | .bulkCommit => (List.finRange 2).map fun j => (Site.bulkCommit j).pc
  | .bulkWait => (List.finRange 2).map fun j => (Site.bulkWait j).pc
  | .exit => (List.finRange 1).map fun j => (Site.exit j).pc
  | .matrixLoadMx | .matrixStoreWr | .loadEl1 | .loadEl2 | .loadEl3 => []

/-- The 24 kinds. -/
def allKinds : List SiteKind :=
  [.elect, .shfl, .mbarInit, .fenceMbarInit, .bar, .load, .mbarArrive, .tensorCopy, .mbarWait,
    .fenceProxy, .store, .trap, .matrixLoad, .warpMma, .matrixMove, .matrixStore, .bulkCommit,
    .bulkWait, .exit, .matrixLoadMx, .matrixStoreWr, .loadEl1, .loadEl2, .loadEl3]

/-- **The scan, evaluated**: for every kind, the instructions of the kind are at the program
counters of the kind's sites, in order. -/
theorem scan : allKinds.all (fun κ => pcsOf κ == sitePcs κ) = true := by
  decide +kernel

/-- **The sites of a kind are exactly the instructions of the kind.** -/
theorem pcsOf_eq (κ : SiteKind) : pcsOf κ = sitePcs κ := by
  have h := List.all_eq_true.mp scan κ (by cases κ <;> decide)
  simpa using h

/-- A site of a scanned kind: the instruction at its program counter is of the kind. -/
theorem kindAt_of_scan {κ : SiteKind} {n : Nat} {f : Fin n → Nat}
    (h : pcsOf κ = (List.finRange n).map f) (j : Fin n) : kindAt 0 (f j) = some κ := by
  apply mem_pcsOf.mp
  rw [h]
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

/-- The instruction at a site of sub-step 0 is of the site's kind. -/
theorem site_kind0 (s : Site) (hs : s.sub = 0) : kindAt 0 s.pc = some s.kind := by
  cases s with
  | elect j => exact kindAt_of_scan (pcsOf_eq .elect) j
  | shfl j => exact kindAt_of_scan (pcsOf_eq .shfl) j
  | mbarInit j => exact kindAt_of_scan (pcsOf_eq .mbarInit) j
  | fenceMbarInit j => exact kindAt_of_scan (pcsOf_eq .fenceMbarInit) j
  | bar j => exact kindAt_of_scan (pcsOf_eq .bar) j
  | load j => exact kindAt_of_scan (pcsOf_eq .load) j
  | mbarArrive j => exact kindAt_of_scan (pcsOf_eq .mbarArrive) j
  | tensorCopy j => exact kindAt_of_scan (pcsOf_eq .tensorCopy) j
  | mbarWait j => exact kindAt_of_scan (pcsOf_eq .mbarWait) j
  | fenceProxy j => exact kindAt_of_scan (pcsOf_eq .fenceProxy) j
  | store j => exact kindAt_of_scan (pcsOf_eq .store) j
  | trap j => exact kindAt_of_scan (pcsOf_eq .trap) j
  | matrixLoad j => exact kindAt_of_scan (pcsOf_eq .matrixLoad) j
  | warpMma j => exact kindAt_of_scan (pcsOf_eq .warpMma) j
  | matrixMove j => exact kindAt_of_scan (pcsOf_eq .matrixMove) j
  | matrixStore j => exact kindAt_of_scan (pcsOf_eq .matrixStore) j
  | bulkCommit j => exact kindAt_of_scan (pcsOf_eq .bulkCommit) j
  | bulkWait j => exact kindAt_of_scan (pcsOf_eq .bulkWait) j
  | exit j => exact kindAt_of_scan (pcsOf_eq .exit) j
  | matrixLoadMx j row => cases hs
  | matrixStoreWr j row => cases hs
  | loadEl1 j v0 => cases hs
  | loadEl2 j v0 v1 => cases hs
  | loadEl3 j v0 v1 v2 => cases hs

/-- The one vector load is the last of the 178 loads. -/
theorem loadEl_pc (j : Fin 1) : [Flow.load_177].getD j.val 0 = (Site.load 177).pc := by
  revert j
  decide

/-- **The instruction at a site's program counter is of the site's kind**, at the site's
sub-step. -/
theorem site_kind (s : Site) : kindAt s.sub s.pc = some s.kind := by
  have key : ∀ {pc : Nat} {κ κ' : SiteKind} {sub : Nat}, kindAt 0 pc = some κ →
      (∀ op, opKind 0 op = some κ → opKind sub op = some κ') → kindAt sub pc = some κ' := by
    intro pc κ κ' sub h hop
    unfold kindAt at h ⊢
    cases hc : kernel.code[pc]? with
    | none => rw [hc] at h; cases h
    | some ins =>
      rw [hc] at h
      exact hop ins.op h
  have hv : ∀ j : Fin 1, kindAt 0 ([Flow.load_177].getD j.val 0) = some .load := fun j => by
    rw [loadEl_pc j]
    exact site_kind0 (.load 177) rfl
  cases s with
  | matrixLoadMx j row =>
    exact key (site_kind0 (.matrixLoad j) rfl) fun op h => opKind_matrixLoad h Nat.one_ne_zero
  | matrixStoreWr j row =>
    exact key (site_kind0 (.matrixStore j) rfl) fun op h => opKind_matrixStore h Nat.one_ne_zero
  | loadEl1 j v0 => exact key (hv j) fun op h => (opKind_load h).1
  | loadEl2 j v0 v1 => exact key (hv j) fun op h => (opKind_load h).2.1
  | loadEl3 j v0 v1 v2 => exact key (hv j) fun op h => (opKind_load h).2.2
  | _ => exact site_kind0 _ rfl

/-- The instruction at a site, with its kind. -/
theorem site_op (s : Site) {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
    opKind s.sub ins.op = some s.kind := by
  have h := site_kind s
  unfold kindAt at h
  rwa [hc] at h

/-! ### Tensor loads and tensor stores among the tensor copies -/

/-- The ordinal of the first tensor store among the tensor copies: `tensorCopy j` is a load
into shared memory for `j < 226` and a store to global memory for `226 ≤ j`. -/
def firstStoreCopy : Nat := 226

theorem pcs_tensorLoad :
    pcsWhere tensorOp =
      ((List.finRange 258).filter fun j => j.val < firstStoreCopy).map fun j =>
        (Site.tensorCopy j).pc := by
  decide +kernel

theorem pcs_tensorStore :
    pcsWhere tensorStoreOp =
      ((List.finRange 258).filter fun j => firstStoreCopy ≤ j.val).map fun j =>
        (Site.tensorCopy j).pc := by
  decide +kernel

/-- A tensor copy before `firstStoreCopy` is a tensor load instruction. -/
theorem tensorCopy_load {j : Fin 258} (hj : j.val < firstStoreCopy) {ins : Instr}
    (hc : kernel.code[(Site.tensorCopy j).pc]? = some ins) : tensorOp ins.op = true := by
  have hm : (Site.tensorCopy j).pc ∈ pcsWhere tensorOp := by
    rw [pcs_tensorLoad]
    exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩
  obtain ⟨ins', hc', hq⟩ := mem_pcsWhere.mp hm
  rw [hc] at hc'
  cases hc'
  exact hq

/-- A tensor copy from `firstStoreCopy` on is a tensor store instruction. -/
theorem tensorCopy_store {j : Fin 258} (hj : firstStoreCopy ≤ j.val) {ins : Instr}
    (hc : kernel.code[(Site.tensorCopy j).pc]? = some ins) : tensorStoreOp ins.op = true := by
  have hm : (Site.tensorCopy j).pc ∈ pcsWhere tensorStoreOp := by
    rw [pcs_tensorStore]
    exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩
  obtain ⟨ins', hc', hq⟩ := mem_pcsWhere.mp hm
  rw [hc] at hc'
  cases hc'
  exact hq

end Ref

end PTX.Kernels.FlashKdaFwd.Proof
