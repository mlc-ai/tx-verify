-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
public import Lemmas.Flow.AccessLocal
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Kernel.Memory

@[expose] public section

/-!
# The read-only input assumption: the sites and the launch bytes

`Assumptions.inputReadOnly` constrains the plain reads at the 37 global loads of the program
(`Assumptions.inputReadSites`).

* The sites are exactly the reads of the program that may read global memory, and each is a load
  of global memory (`kernel_nonShared_reads`, `kernel_sites_global`, `decide +kernel`): a read
  event of global memory is at a site (`read_site_global`).
* So every read of an input byte returns its launch byte (`inputReadValue`), at every event of
  every consistent execution, with no premise about the writes of the execution. In particular
  every read of a `cu_seqlens_q` word returns its launch word (`cuQWordReads`,
  `cuQReadsFromLaunch`).
-/

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Instructions that may read global memory: a load that names global memory or no space. -/
def nonSharedReadOp (op : Op) : Bool :=
  match op with
  | .mem ma => readOp op && (ma.space == some .global || ma.space == none)
  | _ => false

/-- **The reads of the program that may read global memory are at the sites.** -/
theorem kernel_nonShared_reads :
    OpPcsFast kernel.code nonSharedReadOp Assumptions.inputReadSites = true := by
  decide +kernel

/-- **Each site is a load of global memory.** -/
theorem kernel_sites_global : Assumptions.inputReadSites.all (fun pc =>
    (kernel.code[pc]?).any fun ins => loadSpace ins.op == some .global) = true := by
  decide +kernel

theorem inputReadOnly_mem : Assumptions.inputReadOnly ∈ Assumptions.all := by
  simp [Assumptions.all]

/-- A read of global memory is fired at a site. -/
theorem fired_global_site {A : List Assumption} {l : Launch} {g : Nat} {t : TState} {pc : Nat}
    {ins : Instr} {e : Event} {o : Option TState} {a : Acc} {bs : List (Option Byte)}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A l g t ins.op) e o)
    (hk : e.kind = .rd a bs) (hsp : a.loc.space = .global) :
    Assumptions.inputReadSites.contains pc = true := by
  have hr := fires_read_op hf hk
  obtain ⟨ma, hma, hns⟩ := fires_read_global hf hk hsp
  have hm := OpPcsFast.mem kernel_nonShared_reads hc (by
    rw [hma] at hr ⊢
    rcases hns with h | h <;> simp [nonSharedReadOp, hr, h])
  simpa using hm

/-- **A read event of global memory is at a site.** -/
theorem read_site_global {A : List Assumption} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel A m X) {e : EvId} {pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get e = some ⟨pc, .rd a bs⟩)
    (hsp : a.loc.space = .global) : Assumptions.inputReadSites.contains pc = true := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hfi⟩
  · cases hf
  · exact fired_global_site hc hfi rfl hsp

/-- An input byte of the launch's parameters is an input byte of the launch. -/
theorem Pre.inputByte {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {r : Region} (hr : r ∈ p.inputRegions) {loc : Loc} (hl : r.Contains loc) :
    Assumptions.InputByte l m loc :=
  ⟨p, hp, r, hr, hl⟩

/-- **Every read of an input byte returns its launch byte**, by `Assumptions.inputReadOnly`. -/
theorem inputReadValue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bs : List (Option Byte)} (hRead : X.Reads i a bs)
    {v : Value} (hSize : a.size = v.bytes)
    (hIn : ∀ k < a.size, ∃ r ∈ p.inputRegions, r.Contains (a.loc.at k))
    (hLaunch : ∀ k < a.size, m (a.loc.at k) = some (some (v.byteAt k))) :
    bs = v.toBytes.map some := by
  obtain ⟨pc, he⟩ := hRead
  have hLen := hX.read_length (e := .thread i) (.inl ⟨pc, he⟩)
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.size
  · obtain ⟨r, hr, hc⟩ := hIn k hk
    have hsp : a.loc.space = .global := hc.1
    have hs := read_site_global hX he hsp
    rw [hX.asm _ inputReadOnly_mem i pc a bs he hs k hk (hp.inputByte hr hc) _ (hLaunch k hk)]
    simp [Value.toBytes, ← hSize, hk]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [Value.toBytes]; omega)]

/-- Each in-range cumulative query word is an input word. -/
theorem cuQ_input {p : Params} {index : Nat} (hi : index ≤ p.batch) :
    ∀ k < 4, ∃ r ∈ p.inputRegions, r.Contains ((globalLoc (p.cuQBase + 4 * index)).at k) := by
  intro k hk
  refine ⟨⟨p.cuQBase, 4 * (p.batch + 1)⟩, by simp [Params.inputRegions], ?_⟩
  simp only [Region.Contains, globalLoc, Loc.at, true_and]
  omega

/-- **Every read of an in-range `cu_seqlens_q` word returns its launch word.** -/
theorem cuQWordReads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {index : Nat}
    (hi : index ≤ p.batch) : Epilogue.CuQWordReadsFromLaunch p X index :=
  fun _ _ hRead => inputReadValue hp hX hRead rfl (cuQ_input hi) (hp.cuQ index hi)

theorem cuQReadsFromLaunch {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    Epilogue.CuQReadsFromLaunch p X :=
  fun _ hi => cuQWordReads hp hX hi

end
end PTX.Kernels.TmlFa4Fwd
