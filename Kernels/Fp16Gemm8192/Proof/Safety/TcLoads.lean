-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.ThreadUb
public import Kernels.Fp16Gemm8192.Proof.Safety.TmemAccess

@[expose] public section

/-! # The words of the Tensor Memory loads, from the interface

Every word a Tensor Memory load returns has a source write (`TcMma.SourceSafe`) and contains its
value (`TcMma.LoadReadOk`); the kernel's Tensor Memory writes leave single-precision floats, whole
words (`TmemWords`). So every loaded word is a single-precision float (`loadWords_of`), the last
premise of the undefined-behaviour branch (`no_ub`). The Tensor Memory accesses' lifetimes
(`TmemLive`, `tmem_live`) are the access branch's: every access is allocated and done before the
releases of its covering allocations. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every word a Tensor Memory load returns is a single-precision float.** -/
theorem loadWords_of (hX : Consistent L kernel Prod mem0 X) (hw : TmemWords L X)
    (hs : TcMma.SourceSafe L Prod X) : LoadWords X := by
  intro e a vals sh hl v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hcell : TcMma.LoadCell L X e j (tcDataCell L e.1 sh a j) := ⟨a, vals, sh, hl, hj, rfl⟩
  obtain ⟨source, value, hrs, hwr⟩ := (TcMma.sourceSafe_iff.mp hs).1 e j _ hcell
  obtain ⟨word, hword, hc⟩ := hX.tcRead.1 e a vals sh j source _ value hl hcell hrs hwr
  obtain ⟨r, rfl⟩ := hw.2 _ _ _ hwr
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hword
  rw [hword]
  rcases hc with ⟨-, rfl⟩ | ⟨hb, -⟩
  · exact ⟨r, rfl⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb

/-- **The Tensor Memory accesses' lifetimes** (`TmemLive`): every access is allocated and done
before the releases of its covering allocations. -/
theorem tmem_live {P : Params} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hdone : TmemExitDone L X) : TmemLive L X := by
  intro e cell hacc
  obtain ⟨⟨ev, r, he, hσ⟩, hcta, hcol⟩ := access_cell hpre hX ht hacc
  refine ⟨access_allocated hpre hX ht he hσ hcta hcol, fun key rq hrq hcov d hrel => ?_⟩
  have hk := covers_key hpre hX ht hrq hcov
  exact release_done hpre hX ht hdone hrq hrel (by omega)

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
