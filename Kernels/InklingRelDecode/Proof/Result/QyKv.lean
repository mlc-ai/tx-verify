-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxAll
public import Kernels.InklingRelDecode.Proof.Result.WzAll
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof2.Safety.Box

@[expose] public section

/-!
# The B elements of every MMA are numbers (`Qx.ElemRest.b`), on every consistent execution

`Result.Mma.kv_byte` reads a K or V byte through `KvCopies` and `KvOrder`, which are stated for
complete executions. Here the copy is the one `Wz.KvCopiesF` names for the block the issued MMA
reads, the order is `Wz.kvOrderF` at the MMA's footprint, and the copied byte is a byte of the
cache by the copy's spec (`Proof2.copy_form`: every tensor copy copies a K or V box of a
slab of a block that exists) and `kv_copy_written`. The two bytes of an element are written by
one copy at one slot of its box, so they are the two bytes of one bf16 number.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts threadCode)
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
  (hR : Interface.RoleReads L X) (hE : Interface.Bar1Exits L X)
  (hp : Interface.NumPreRead Q L X) (hn : Interface.NumWordRead Q L X)
  (hbox : Safety.BoxInBounds X) (G : Sr.SrPkg L kernel Assumptions.all mem0 X)
  (hkc : Wz.KvCopiesF Q L X) (hMB : Mma.MmaBcast L X)
include hpre hX hf hT hR hE hp hn hbox G hkc hMB

omit hn in
/-- **The two bytes of a K or V element an MMA reads are the bytes of one bf16 number.** An MMA
event of block `i` reads, at the B operand bytes `b0` and `b0 + 1`, the two bytes of element
`(n, e)` of the K or V tile of ring slot `i % 3`. -/
theorem kv_elem_bytes {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (hg : g < L.threads) (hissue : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    {d : Mma.D} {i : Nat} (hAt : AtMma Q L X (g, k) d) (hblk : MmaBlock d i)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands (g, k) = some ops)
    {isV n e b0 : Nat} (hV : isV ≤ 1) (hn' : n < 128) (he : e < 128)
    (hl : ∀ z, z < 2 → sp.byteLoc .b (b0 + z) =
      some ⟨.shared, g / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩) :
    ∃ v : ℝ, ∀ z, z < 2 → ops.b[b0 + z]? = some (some ((Value.float .bf16 v).byteAt z)) := by
  obtain ⟨⟨gc, kc⟩, o, a, col, row, bar, hTI, hobs, hcb, hspec⟩ :=
    hkc.exists_copy (m := (g, k)) isV (n / 64) (e / 64) hg ⟨dst, sp, acc, mask, pc, hissue⟩ hAt
      hblk hV (by omega) (by omega)
  obtain ⟨pcc, hec⟩ := hTI
  obtain ⟨r, sl, kvh, isV', hh', dst', bar', hr, hsl, hkvh, hV', hH', hspec'⟩ :=
    Proof2.copy_form hpre hX hec
  have hsb := hpre.sharedAlignment
  refine ⟨Q.kv (Q.page r sl * Q.pageRows + kvh * Q.headRows + n % 64)
    (kvh * Q.headCols + 128 * isV' + 64 * hh' + e % 64), fun z hz => ?_⟩
  have hwl : TensorCopy.writeLoc o.spec (e % 64) (n % 64) z =
      some ⟨.shared, g / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩ := by
    rw [hspec]
    exact copy_loc_kv Q _ _ isV _ _ _ bar (by omega) hn' he hz
  obtain ⟨obs, hr', hget⟩ := hX.mma_read_exists (isB := true) ⟨pc, hissue⟩ hops
    (by simpa using hl z hz)
  simp only [↓reduceIte] at hget
  obtain ⟨⟨b, hwb⟩, hv, horder⟩ := Wz.kvOrderF hpre hX hf hT hR hE hp hbox G hMB hAt hblk hcb hobs
    ⟨pcc, hec⟩ hwl hr'.1
  have hobsb : obs = some b := by
    have hw : X.MemWrites (.async (gc, kc) (.write (.load (e % 64) (n % 64) z)))
        { loc := ⟨.shared, g / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩, size := 1 }
        [b] :=
      ⟨o, a, b, hobs, ⟨pcc, hec⟩, hwl, hwb, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have := read_byte_of_write hX hr' hw (by simp [Acc.Covers, Loc.InRange]) hv horder
    simpa [wbyte] using this
  have hval := kv_copy_written hpre hf hX (r := r) (s := sl) (kvh := kvh) (isV := isV')
    (hh := hh') hr hsl (by unfold kvHeads at hkvh; omega) hV' hH' hobs hspec' (by omega)
    (by omega) hz hwb
  rw [hget, hobsb, hval]

omit hn in
/-- **`Qx.ElemRest.b`**: every B element of every MMA with recorded operands is a number. -/
theorem elemB_of : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    {d : Mma.D} {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {n kk : Nat},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) →
    (d.site = .qk j ∨ d.site = .pv j) →
    X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → n < 128 → kk < 16 →
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b n kk = .ok y := by
  intro g k pc dst sp acc mask d P j ops n kk hg he hσ hs _ hops hn' hk
  have hEnv := EvW.mmEnv_of_pre hpre
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d', P', j', hσ', hI, hs', hq, -, -, -⟩ | ⟨d', P', j', hσ', hI, hs', hq, -, -, -⟩
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    obtain ⟨v, hv⟩ := kv_elem_bytes hpre hX hf hT hR hE hp hbox G hkc hMB hg he (i := d.i)
      ⟨P, hσ⟩ (Or.inl ⟨j', hs', rfl⟩) hops (isV := 0) (n := n) (e := 16 * j'.val + kk)
      (b0 := 32 * n + 2 * kk) (by omega) hn' (by omega) (fun z hz => by
        rw [qk_b_loc_eq hEnv hq.desc (Nat.mod_lt _ (by omega)) j'.isLt hq.b hn' hk hz, hq.low])
    refine ⟨v, element_bf16 ?_ ?_⟩
    · rw [show 2 * (n * 16 + kk) = 32 * n + 2 * kk + 0 by ring]
      exact hv 0 (by omega)
    · rw [show 2 * (n * 16 + kk) + 1 = 32 * n + 2 * kk + 1 by ring]
      exact hv 1 (by omega)
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    obtain ⟨h1, -, -⟩ := hI.pv (by simp [Mma.PvSite, hs'])
    obtain ⟨v, hv⟩ := kv_elem_bytes hpre hX hf hT hR hE hp hbox G hkc hMB hg he (i := d.i - 1)
      ⟨P, hσ⟩ (Or.inr ⟨j', hs', by omega⟩) hops (isV := 1) (n := 16 * j'.val + kk) (e := n)
      (b0 := 32 * n + 2 * kk) (le_refl _) (by omega) hn' (fun z hz => by
        rw [pv_b_loc_eq hEnv hq.desc (Nat.mod_lt _ (by omega)) j'.isLt hq.b hn' hk hz, hq.low])
    refine ⟨v, element_bf16 ?_ ?_⟩
    · rw [show 2 * (n * 16 + kk) = 32 * n + 2 * kk + 0 by ring]
      exact hv 0 (by omega)
    · rw [show 2 * (n * 16 + kk) + 1 = 32 * n + 2 * kk + 1 by ring]
      exact hv 1 (by omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
