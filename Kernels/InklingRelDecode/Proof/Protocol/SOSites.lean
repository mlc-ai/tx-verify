-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ProtocolThreads

@[expose] public section

/-!
# Which instructions of the kernel poll, arrive on and commit to an mbarrier

A global audit of the decoded program, by `decide +kernel`, stated through the machines' own site
accessors (`Site.pc`), so that no literal program counter occurs:

* `waitSites`: the instructions that are `mbarrier.try_wait.parity` are exactly the poll sites of
  the machines: the softmax region's `waitS` (`s_ready`) and `waitO` (`o_done`), the loader's
  `wait` (`kv_empty`), the MMA warp's `kvWait` (`kv_ready`) and `pWait` (`p_ready`), and the
  epilogue's `wait` (`o_final`);
* `arriveSites`: the instructions that are `mbarrier.arrive` are the three preload arrivals of the
  prologue (`arr0`, `arr1`, `arr2`), the loader's `arrive` and the softmax region's `arrive`;
* `commitSites`: the `tcgen05.commit`s are the MMA warp's four.

From them, an event of a thread that fires at a state whose site is none of those sites is not a
poll, an arrival or a commit (`Fired.notWait` ...), which is what the per-thread counts of the
handshake need at the sites that have no event shape (`Sm.Shape` is `True` there).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- The poll sites of the machines. -/
def waitSites : List Nat :=
  [Sm.Site.waitS.pc, Sm.Site.waitO.pc, Loader.Site.wait.pc, Mma.Site.kvWait.pc,
    Mma.Site.pWait.pc, Epi.Site.wait.pc]

/-- The arrival sites of the machines. -/
def arriveSites : List Nat :=
  [ProA.Site.arr0.pc, ProA.Site.arr1.pc, ProA.Site.arr2.pc, Sm.Site.arrive.pc,
    Loader.Site.arrive.pc]

/-- **The polls of the program are the machines' poll sites.** -/
theorem wait_sites : (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .mbarWait .. => true
      | _ => false)).map (·.2) = waitSites := by
  decide +kernel

/-- **The arrivals of the program are the machines' arrival sites.** -/
theorem arrive_sites : (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .mbarArrive .. => true
      | _ => false)).map (·.2) = arriveSites := by
  decide +kernel

/-- An instruction of the program that has a property `P` shared by the filtered instructions is
at a site of the filter. -/
theorem site_of_filter {P : Op → Bool} {sites : List Nat}
    (h : (kernel.code.zipIdx.filter (fun p => P p.1.op)).map (·.2) = sites) {pc : Nat}
    {ins : Instr} (hc : kernel.code[pc]? = some ins) (hp : P ins.op = true) : pc ∈ sites := by
  rw [← h]
  refine List.mem_map.mpr ⟨(ins, pc), List.mem_filter.mpr ⟨?_, by simpa using hp⟩, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?]
  simpa using hc

/-- A poll of the program is at a poll site. -/
theorem wait_pc {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    {p b : Nat} {o : Int} {par : Opnd} {a : Bool} {s : MbarScope}
    (hw : ins.op = .mbarWait p b o par a s) : pc ∈ waitSites :=
  site_of_filter (P := fun op => match op with | .mbarWait .. => true | _ => false) wait_sites
    hc (by simp [hw])

end

end PTX.Kernels.InklingRelDecode.Proof.SO
