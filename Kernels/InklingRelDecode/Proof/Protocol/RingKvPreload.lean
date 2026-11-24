-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.KvSingle
public import Kernels.InklingRelDecode.Proof.Protocol.RingLoaderExec
public import Kernels.InklingRelDecode.Proof.Interface.ProtocolThreads

@[expose] public section

/-!
# The prologue's preload of a KV slot: what the default partition has to supply

The default partition's prologue (warps 0 to 3, `ProA`) preloads the first `np = num_pre ≤ 3`
blocks: block `j < np` is staged in slot `j` without any wait (the barriers are fresh). Per block
it issues

* **one** `mbarrier.arrive.expect_tx` of 65536 bytes, count 1, release at CTA scope, on
  `kv_ready j` (`ProA.shape_arr`), and
* **eight** tensor copies of the `kv_rows` map (`ProA.shape_ptc`): four sites (`ptcSite (4 j + c)`,
  `c < 4`: K slab 0, V slab 0, K slab 1, V slab 1), each executed by the elected lane of warp 0 and
  of warp 1, which differ in the destination (`+ 16384 (warp % 2)`) and the origin column: the K
  halves and V halves of the slab. Each completes on `kv_ready j` with 8192 bytes (the `(64, 64)`
  bf16 box of `mapKv`).

`EvD.Bar.loc L cta (.kvReady s)` is the barrier `kvReady L cta s` of the loader and the MMA warp
(`bar_loc_kvReady`), and the arrival's 65536 bytes are the eight copies' (`tx_balance`).

The default partition is not a `Flow.Machine` yet (`ProA` is a code machine without the framework's
event/frame interface, `Epi` and the softmax region are separate), so the events' *identity* is
not available: which threads execute the sites, that they execute them once, and that no other
default-partition event arrives on or copies to a ring barrier. `PreloadFacts` is that input,
as one structure: the arrival and the eight copies of slot `s` of the CTA as events of the
execution, with the shapes `ProA.shape_arr` and `ProA.shape_ptc` give (the two bits of them that
need the prologue machine's run invariant, the map address and the shared-memory word of the
copy's destination, are the gap rows of the development notes), and the completeness of the list. It
supplies the prologue half of `Kv.Hyp` (`δ`, `pArr`, `pCp`, `pre_cta`, `pre_ne`, `pre_inj`, and
`issue`'s prologue case), see `PreloadFacts.slot`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Kv
open PTX PTX.Flow AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section

/-- The arrival's bytes are the eight copies'. -/
theorem tx_balance : txBytes = 8 * copyBytes := by decide

/-- **What the default partition supplies for slot `s` of the CTA `cta`.** -/
structure PreloadFacts (Q : Params) (L : Launch) (X : Execution) (cta s : Nat) where
  /-- The prologue's `expect_tx` arrival. -/
  arr : EvId
  /-- The prologue's copies: site `c < 4`, warp `w < 2`. -/
  cp : Fin 4 → Fin 2 → EvId
  /-- `ProA.shape_arr`: 65536 bytes, one arrival, release, CTA scope, on `kv_ready s`. -/
  arr_shape : ∃ pc, X.get arr = some ⟨pc, .arrive (kvReady L cta s) txBytes 1 true .cta⟩
  /-- `ProA.shape_ptc` (and the map): a tile copy completing on `kv_ready s`, 8192 bytes. -/
  cp_shape : ∀ c w, ∃ pc a sp, X.get (cp c w) = some ⟨pc, .tensorIssue a sp⟩ ∧
    sp.mbar = kvReady L cta s ∧ TensorTransfer.bytes sp.descriptor = copyBytes
  /-- The arrival and the copies are threads of the CTA: the copy of warp `w` is warp `w`'s. -/
  arr_cta : arr.1 / L.block = cta ∧ arr.1 < L.threads
  cp_cta : ∀ c w, (cp c w).1 / L.block = cta ∧ (cp c w).1 < L.threads
  cp_warp : ∀ c w, (cp c w).1 % L.block / 32 = w.val
  /-- The eight copies are distinct events. -/
  cp_inj : ∀ c w c' w', cp c w = cp c' w' → c = c' ∧ w = w'
  /-- Completeness: an arrival on `kv_ready s` of a thread that is not in the loader role at that
  event is the prologue's; a copy completing on it of a thread that is not in the loader role is
  one of the prologue's eight. -/
  arr_all : ∀ {g k pc tx cnt rel sc}, X.get (g, k) = some ⟨pc, .arrive (kvReady L cta s) tx cnt
    rel sc⟩ → (∃ d P, wAt Q L X g k = some (some (.loader d P))) ∨ (g, k) = arr
  cp_all : ∀ {g k pc a sp}, X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ →
    sp.mbar = kvReady L cta s →
    (∃ d P, wAt Q L X g k = some (some (.loader d P))) ∨ ∃ c w, (g, k) = cp c w

/-- The eight copies as a function of `Fin 8`: copy `2 c + w`. -/
def PreloadFacts.copy {Q : Params} {L : Launch} {X : Execution} {cta s : Nat}
    (P : PreloadFacts Q L X cta s)
    (i : Fin 8) : EvId :=
  P.cp ⟨i.val / 2, by omega⟩ ⟨i.val % 2, by omega⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Kv
