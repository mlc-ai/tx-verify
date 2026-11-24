-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerStoreTile
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader

@[expose] public section

/-! # A tensor store's output tile, along an execution

A tensor store is a consumer's TMA store of a slice (`Consumer.out_site`), by its warp group's
first thread, at the tile of its task (`Consumer.TileRel`), whose box starts at the slice's
column and the thread's rows (`Consumer.tma_origin`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **A tensor store's tile.** -/
theorem store_tile_fact {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k pc a : Nat} {sp : TensorStore.Spec} {c : Consumer.D} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tensorStore a sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) :
    ∃ s : Fin 8, c.site = .tma s ∧ Consumer.first L g = true ∧ c.m < 16 ∧ c.n < 32 ∧
      sp.rows = none ∧ sp.reduce = none ∧ (∀ i : Fin (sp.outer + 1), sp.origin i =
        if i.val = 0 then ((256 * c.n + 32 * s.val : Nat) : Int)
        else if i.val = 1 then
          ((512 * c.m + 128 * (Consumer.tidOf L g / 32 / 4) + 256 * (g / L.block % 2) : Nat) : Int)
        else 0) ∧
      Consumer.TileAt L g ((X.tr g).take k) (okPolls (clcResp L g) ((X.tr g).take k) - 1) c.m c.n :=
        by
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨s, hs⟩ := (Consumer.out_site hc hf).2.1 a sp rfl
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hti := (consInv hpre hg htr k _ hσ).2.2.2.2.2.2.2.2.2.1
  have hti2 := hti.2.1 (by rw [hs]; simp)
  simp only [Consumer.epoch, hs, reduceCtorEq, ↓reduceIte] at hti2
  obtain ⟨hrow, hred, ho⟩ := Consumer.tma_origin hat hinv.1 hinv.2.1 hc hf hs a sp rfl
  exact ⟨s, hs, hti.2.2.2.2.2 s (.inr hs), hinv.1.m, hinv.1.n, hrow, hred, ho, hti2⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
