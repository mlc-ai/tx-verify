-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutPremises
public import Kernels.InklingRelDecode.Proof.Result.OutOrigin
public import Kernels.InklingRelDecode.Proof.Result.RsEpiLoad

@[expose] public section

/-!
# Every global write is a store of `Spec`'s output (result layer, part 2d)

`write_spec`: a write of a consistent complete execution to global memory is a store of word `d`
of `OPart[split, token, head]` of a valid row of a request, with the bytes of `oWord` (the f32
float of `Spec.oPart`, or the zero word of the `num_iters = 0` path), or a store of
`LsePart[split, token, head]` with the bytes of `lseWordOf` (the f32 float of `Spec.lsePart`, or
the `-inf` pattern for an empty row).

The proof reads the thread layer's classification of the write (`ThreadFacts.global_wr`: the
epilogue state, `Epi.Means`, the store site, the word) and the values of the epilogue
(`OutEpi.lean`, from `Inputs.rowIn`, `Inputs.skip`, and `OutLoad.load_word`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma PTX.TcMma
open Classical

noncomputable section

/-- The value the store of word `d` of `OPart[split, token, head]` writes: the f32 float of
`Spec.oPart`, or the zero word when the split has no block. -/
def oWord (P : Params) (r s tok head d : Nat) : Value :=
  if P.numIters r s = 0 then b32 0 else fl (oPart P r s tok head d)

/-- The value the store of `LsePart[split, token, head]` writes: the f32 float of `Spec.lsePart`,
or the `-inf` pattern for a row with no visible key. -/
def lseWordOf (P : Params) (r s tok head : Nat) : Value :=
  if rowSum P r s tok head = 0 then b32 4286578688 else fl (lsePart P r s tok head)

theorem oWord_bytes (P : Params) (r s tok head d : Nat) : (oWord P r s tok head d).bytes = 4 := by
  unfold oWord
  split_ifs <;> rfl

theorem lseWordOf_bytes (P : Params) (r s tok head : Nat) :
    (lseWordOf P r s tok head).bytes = 4 := by
  unfold lseWordOf
  split_ifs <;> rfl

/-- The store of a four-byte value writes it unchanged. -/
theorem storeValue_four {v w : Value} (h : v.bytes = 4) (hv : storeValue 32 v = .ok w) :
    w = v := by
  rw [storeValue_of_bytes (by simpa using h)] at hv
  exact (Except.ok.inj hv).symm

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A valid row's coordinates are in range.** -/
theorem row_valid {g : Nat} {pr : Epi.Prm} (hpre : Pre Q L mem0) (hg : g < L.threads)
    (hm : Epi.Means Q L g pr) (hrv : pr.rv = true) :
    reqOf L g < Q.b ∧ splitOf L g < Q.splits ∧ Epi.tokM (g % L.block) < Q.qLen (reqOf L g) ∧
      Epi.outHead L g < heads := by
  obtain ⟨hx, hz, -, hh⟩ := Epi.row_coords hpre hg hm hrv
  have h1 := of_decide_eq_true (hm.rv.symm.trans hrv)
  exact ⟨hz, hx, h1.2, hh⟩

/-- **The epilogue state of a write is the default partition's and satisfies the invariant.** -/
theorem epi_inv (hS : ∀ g < L.threads, (Interface.threadCode L g Q).Sound)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {g k pc : Nat} {a : Acc} {bs : List Byte} {d : Epi.D}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : Interface.St Q L X g k = some (some (.d (.epi d)))) :
    g % L.block < 128 ∧ Epi.Inv d := by
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  exact ⟨hinv.1, hinv.2.1⟩

/-- **A store of `OPart` writes `Spec`'s value.** -/
theorem oStore_value (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hin : Inputs Q L mem0 X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    {d : Epi.D} (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : Interface.St Q L X g k = some (some (.d (.epi d)))) (hm : Epi.Means Q L g d.pr)
    (hrv : d.pr.rv = true) {j : Fin 64} (hj : d.site = .stO j) {v : Value}
    (hv : storeValue 32 (d.word j) = .ok v) :
    v = oWord Q (reqOf L g) (splitOf L g) (Epi.tokM (g % L.block)) (Epi.outHead L g)
      (Epi.outCol0 L g + j) := by
  have hS := Interface.sound_all hpre hin.smOb
  have hf := Interface.threadFacts hpre hin.smOb hX hin.premises
  obtain ⟨hdef, hinv⟩ := epi_inv hS hX he hσ
  obtain ⟨i, hpr, hrow⟩ := rowIn_of_smExit (fun h1 h2 h3 => hin.smExit hg h1 h2 h3) hσ hrv
  have hsk := skip_of hpre hf hg hσ
  by_cases h0 : d.sk = true
  · have hn := hsk.1 h0
    have hw : d.word j = b32 0 := word_sk h0 j
    rw [storeValue_four (v := d.word j) (by rw [hw]; rfl) hv, hw]
    simp [oWord, hn]
  · have h0' : d.sk = false := by simpa using h0
    have hn : Q.numIters (reqOf L g) (splitOf L g) ≠ 0 := fun h => h0 (hsk.2 h)
    obtain ⟨k0, pc0, d0, hσ0, hs0, hpr0, hld⟩ :=
      ld_event' hX hf hg k d hσ h0' (by rw [hj]; show 3 ≤ 5 + j.val; omega)
    obtain ⟨m, pcm, dst, sp, acc, mask, dm, P, hmg, hcta, hem, hσm, hs, hi, htm, hrs⟩ :=
      hin.oSource hg hσ hrv h0' hσ0 hs0 hpr0 hld
    have hlen := hinv.len (by rw [hj]; trivial) h0'
    have hc := load_word hpre hf hX hcomp hin.kvCopies hin.kvOrder hin.mmaWords hin.pTile
      hin.oAcc hdef hm hrv hlen hld hmg hcta hem hσm hs (by omega) hi htm hrs
    have hw := word_oPart hpre.scalePos hpre.splitsPos hrow hpr h0' hc j.isLt
    rw [storeValue_four (v := d.word j) (by rw [hw]; rfl) hv, hw]
    simp [oWord, hn]

/-- **A store of `LsePart` writes `Spec`'s value.** -/
theorem lseStore_value (hpre : Pre Q L mem0) (hin : Inputs Q L mem0 X) {g k : Nat} {d : Epi.D}
    (hg : g < L.threads) (hσ : Interface.St Q L X g k = some (some (.d (.epi d))))
    (hrv : d.pr.rv = true) {v : Value} (hv : storeValue 32 d.pr.lseWord = .ok v) :
    v = lseWordOf Q (reqOf L g) (splitOf L g) (Epi.tokM (g % L.block)) (Epi.outHead L g) := by
  obtain ⟨i, hpr, hrow⟩ := rowIn_of_smExit (fun h1 h2 h3 => hin.smExit hg h1 h2 h3) hσ hrv
  have hw : d.pr.lseWord = lseWordOf Q (reqOf L g) (splitOf L g) (Epi.tokM (g % L.block))
      (Epi.outHead L g) := by
    unfold lseWordOf
    by_cases h0 : rowSum Q (reqOf L g) (splitOf L g) (Epi.tokM (g % L.block))
        (Epi.outHead L g) = 0
    · have he := eq0_of_empty hrow hpre.scalePos hpre.splitsPos h0 0
      simp only [h0, ↓reduceIte]
      show ({ d.pr with bw := 0 } : Epi.Prm).lseWord = _
      unfold Epi.Prm.lseWord
      rw [hpr, he]
      rfl
    · simp only [h0, ↓reduceIte]
      exact lseWord_lsePart hpre.scalePos hpre.splitsPos hrow hpr h0 0
  rw [storeValue_four (v := d.pr.lseWord) (by rw [hw]; exact lseWordOf_bytes _ _ _ _ _) hv, hw]

/-- **A global write is a store of `Spec`'s output value.** The write is word `dc` of
`OPart[split, token, head]` of a valid row, with the bytes of `oWord`, or `LsePart[split, token,
head]`, with the bytes of `lseWordOf`. -/
theorem write_spec (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hin : Inputs Q L mem0 X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hsp : a.loc.space = .global) :
    ∃ r s tok head, r < Q.b ∧ s < Q.splits ∧ tok < Q.qLen r ∧ head < heads ∧
      ((∃ dc, dc < headDim ∧ a = EvD.wordAcc (oLoc Q s (Q.qStart r + tok) head dc) ∧
          bs = (oWord Q r s tok head dc).toBytes) ∨
        (a = EvD.wordAcc (lseLoc Q s (Q.qStart r + tok) head) ∧
          bs = (lseWordOf Q r s tok head).toBytes)) := by
  have hf := Interface.threadFacts hpre hin.smOb hX hin.premises
  obtain ⟨d, hσ, -, hm, hrv, hcase⟩ := hf.global_wr hg he hsp
  obtain ⟨hr, hs, ht, hh⟩ := row_valid hpre hg hm hrv
  refine ⟨reqOf L g, splitOf L g, Epi.tokM (g % L.block), Epi.outHead L g, hr, hs, ht, hh, ?_⟩
  rcases hcase with ⟨j, hj, v, hv, hbs, ha⟩ | ⟨hj, v, hv, hbs, ha⟩
  · refine .inl ⟨Epi.outCol0 L g + j, Interface.col_lt L g j, ha, ?_⟩
    rw [hbs, oStore_value hpre hX hcomp hin hg he hσ hm hrv hj hv]
  · refine .inr ⟨ha, ?_⟩
    rw [hbs, lseStore_value hpre hin hg hσ hrv hv]

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
