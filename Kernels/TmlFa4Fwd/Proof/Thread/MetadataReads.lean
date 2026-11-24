-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocal
import Lemmas.Flow.ElemAccess
import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

/-- The three launch metadata arrays read by the thread roles. -/
inductive MetadataKind
  | cuQ
  | usedK
  | pageTable

private def metadataSites : MetadataKind → List Nat
  | .cuQ => [186, 245, 381, 382, 1750, 1805, 1940, 1999, 2112, 2113, 2653, 2707,
      2776, 2835, 2953, 2954, 2989, 3043, 3110, 3169, 3369, 3370, 7621, 7677,
      7761, 7821, 7955, 7956, 9089, 9144]
  | .usedK => [385, 2116, 3373, 7959]
  | .pageTable => [503, 946, 1416]

/-- An actual metadata observation, classified by the launch array supplying its address. -/
@[no_expose] def MetadataRead (X : Execution) (i : EvId) (kind : MetadataKind)
    (a : Acc) (bytes : List (Option Byte)) : Prop :=
  ∃ site ∈ metadataSites kind, X.get i = some ⟨site, .rd a bytes⟩

theorem MetadataRead.reads {X : Execution} {i : EvId} {kind : MetadataKind}
    {a : Acc} {bytes : List (Option Byte)} (h : MetadataRead X i kind a bytes) :
    X.Reads i a bytes := by
  obtain ⟨site, _, he⟩ := h
  exact ⟨site, he⟩

/-- A later observation of the same read site agrees with its replayed head payload
when the following suffix stays beyond that site. -/
theorem metadataReadPayloadOfSuffix {X : Execution} {g pos j site : Nat}
    {a b : Acc} {bytes data : List (Option Byte)}
    (hPos : pos ≤ j) (he : X.get (g, j) = some ⟨site, .rd a bytes⟩)
    (hRead : X.get (g, pos) = some ⟨site, .rd b data⟩)
    (hSuffix : ∀ e ∈ (X.tr g).drop (pos + 1), site < e.pc) :
    a = b ∧ bytes = data := by
  have eq : j = pos := by
    by_contra hNe
    have hAfter : pos + 1 ≤ j := by omega
    have hMem : (⟨site, .rd a bytes⟩ : Event) ∈ (X.tr g).drop (pos + 1) := by
      apply List.mem_of_getElem? (i := j - (pos + 1))
      rwa [List.getElem?_drop, Nat.add_sub_of_le hAfter]
    exact (Nat.lt_irrefl site) (hSuffix _ hMem)
  rw [eq] at he
  exact Kind.rd.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hRead)))

private theorem metadataSiteAudit :
    OpPcsFast kernel.code (fun op => loadSpace op == some .global)
      (metadataSites .cuQ ++ metadataSites .usedK ++ metadataSites .pageTable) = true := by
  decide +kernel

private def isMetadataWord (op : Op) : Bool :=
  match op with
  | .mem a => (a.rule == some .threadAccess) && (a.kind == .load) && (a.sem == .weak) &&
      !a.nc && (a.elem.width == 32) &&
      match a.addr.base with
      | .reg .. => true
      | _ => false
  | _ => false

private theorem metadataWordAudit :
    kernel.code.all (fun i => (loadSpace i.op != some .global) || isMetadataWord i.op) = true := by
  decide +kernel

/-- Every actual global load is a four-byte metadata read. -/
theorem globalMetadataRead {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (hRead : X.Reads i a bytes) (hGlobal : a.loc.space = .global) :
    (∃ kind, MetadataRead X i kind a bytes) ∧ a.size = 4 := by
  obtain ⟨site, ins, he, hc, hLoad, _⟩ :=
    Loader.nonlocalReadInstruction hX hRead (by rw [hGlobal]; decide)
  rw [hGlobal] at hLoad
  have hSite := OpPcsFast.mem metadataSiteAudit hc (by rw [hLoad]; rfl)
  have hShape := List.all_eq_true.mp metadataWordAudit ins (List.mem_of_getElem? hc)
  simp only [hLoad, bne_self_eq_false, Bool.false_or] at hShape
  constructor
  · rcases List.mem_append.mp hSite with hQK | hPage
    · rcases List.mem_append.mp hQK with hCuQ | hK
      · exact ⟨.cuQ, site, hCuQ, he⟩
      · exact ⟨.usedK, site, hK, he⟩
    · exact ⟨.pageTable, site, hPage, he⟩
  · rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, actual, _, _, hCode, hf⟩
    · cases hBad
    have hSame : actual = ins := Option.some.inj (hCode.symm.trans hc)
    subst actual
    cases hOp : ins.op <;> simp only [hOp, isMetadataWord, Bool.false_eq_true] at hShape
    case mem ma =>
      obtain ⟨base, width, hBase⟩ : ∃ base width, ma.addr.base = .reg base width := by
        cases hBase : ma.addr.base <;> simp [hBase] at hShape
        exact ⟨_, _, rfl⟩
      simp only [hBase, Bool.and_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hShape
      rw [hOp] at hf hLoad
      have hLoc : ma.locSpace? = some .global := by
        simpa [loadSpace, hShape.1.1.1.2] using hLoad
      have hSize := fires_ld_size hf rfl hShape.1.1.1.1 hLoc hBase
        hShape.1.1.1.2 hShape.1.2 hShape.1.1.2
      rw [hShape.2] at hSize
      exact hSize

end PTX.Kernels.TmlFa4Fwd.Thread
