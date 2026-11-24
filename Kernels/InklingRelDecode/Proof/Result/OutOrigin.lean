-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutIssued
public import Kernels.InklingRelDecode.Proof.Result.OutSm

@[expose] public section

/-!
# Where an epilogue state comes from (result layer, part 2g)

The epilogue's registers (`Epi.Prm`) and its branch flag (`Epi.D.sk`) are the bridge's of the
softmax state that left the loop: along a thread's run the epilogue keeps them (`Epi.next` keeps
`pr` and `sk`), and the epilogue is entered only from such a state (`DComp.exitNext`).

* `epi_origin`: an epilogue state has an earlier softmax state `dsm` (event `k1`) whose successor
  is the epilogue's first state, with the same registers and flag.
* `rowIn_of_smExit`: from the softmax region's statement about its last state (`Sm.Corr` of the
  row's blocks, the scale register), the epilogue's registers are the bridge's of a `RowIn`.
* `skip_of`: the epilogue skips the load exactly when the split has no block (the bridge's
  `num_iters < 1` test on `num_iters`, which `SmMeans` gives as `Spec.numIters`).
* `ld_event`: an epilogue state past the load carries the words of an earlier `tcgen05.ld` event.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The state after an event is the machine's successor. -/
theorem st_succ {k : Nat} {e : Event} {s0 s : Interface.TSt} (he : (X.tr g)[k]? = some e)
    (h0 : Interface.St Q L X g k = some (some s0))
    (hn : (Interface.threadCode L g Q).next s0 e = some (some s)) :
    Interface.St Q L X g (k + 1) = some (some s) := by
  show Frame.stateAt (Interface.code L Q) X g (k + 1) = _
  rw [Frame.stateAt_succ he]
  have h0' : Frame.stateAt (Interface.code L Q) X g k = some (some s0) := h0
  rw [h0']
  exact hn

/-- **An epilogue state comes from a softmax state that left the loop.** -/
theorem epi_origin : ∀ (k : Nat) (d : Epi.D),
    Interface.St Q L X g k = some (some (.d (.epi d))) →
    ∃ (k1 : Nat) (dsm : Sm.D) (d1 : Epi.D),
      Interface.St Q L X g k1 = some (some (.d (.sm dsm))) ∧
      Interface.St Q L X g (k1 + 1) = some (some (.d (.epi d1))) ∧
      d1.pr = { d.pr with bw := 0 } ∧ d1.sk = d.sk ∧
      d1 = (if (DComp.exitIn L g dsm).skip then
          Epi.D.startSk (Br.prm (DComp.exitIn L g dsm))
        else Epi.D.start (Br.prm (DComp.exitIn L g dsm))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hσ
    have hne : (Interface.TSt.d (.epi d)) ≠ (Interface.code L Q g).init := by
      simp only []
      split_ifs <;> simp
    obtain ⟨k0, e, s0, hk0, he, hσ0, hn⟩ := Interface.stateAt_pred hσ hne
    rcases epi_pred hn with ⟨d0, rfl, hnx⟩ | ⟨dsm, rfl, hd⟩
    · obtain ⟨hpr, hsk, -, -⟩ := next_site hnx
      obtain ⟨k1, dsm, d1, h1, h2, h3, h4, h5⟩ := ih k0 hk0 d0 hσ0
      refine ⟨k1, dsm, d1, h1, h2, ?_, h4.trans hsk.symm, h5⟩
      rw [h3, hpr]
    · refine ⟨k0, dsm, d, hσ0, st_succ he hσ0 hn, ?_, rfl, hd⟩
      rw [hd]
      split_ifs <;> rfl

/-- **The epilogue's registers are the bridge's `RowIn`**, from the softmax region's last state:
if the softmax state that goes straight into the epilogue has the scale register of the launch and
the running maximum and sum of the row's blocks, the epilogue's `Prm` is `Br.prm` of an input
with that row's scale, row sum and row maximum. -/
theorem rowIn_of_smExit
    (hsm : ∀ {k : Nat} {dsm : Sm.D} {d : Epi.D},
      Interface.St Q L X g k = some (some (.d (.sm dsm))) →
      Interface.St Q L X g (k + 1) = some (some (.d (.epi d))) → d.pr.rv = true →
      dsm.e.sc = Q.scale ∧ Sm.Corr (sl Q) (blocks0 Q (reqOf L g) (splitOf L g)
        (Epi.tokM (g % L.block)) (Epi.outHead L g)) dsm)
    {k : Nat} {d : Epi.D} (hσ : Interface.St Q L X g k = some (some (.d (.epi d))))
    (hrv : d.pr.rv = true) :
    ∃ i : Br.In, { d.pr with bw := 0 } = Br.prm i ∧ RowIn Q i (reqOf L g) (splitOf L g)
      (Epi.tokM (g % L.block)) (Epi.outHead L g) := by
  obtain ⟨k1, dsm, d1, h1, h2, h3, -, h5⟩ := epi_origin k d hσ
  obtain ⟨hsc, hc⟩ := hsm h1 h2 (by rw [h3]; exact hrv)
  refine ⟨DComp.exitIn L g dsm, ?_, rowIn_of_corr hsc hc⟩
  rw [← h3, h5]
  split_ifs <;> rfl

theorem ceil_div_le (x m : Nat) (hm : 0 < m) : (x + (m - 1)) / m ≤ x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)]
  · apply Nat.div_le_of_le_mul
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith

/-- The number of blocks of a split is a non-negative 32-bit integer. -/
theorem numIters_lt (hpre : Pre Q L mem0) {r : Nat} (hr : r < Q.b) (s : Nat) :
    Q.numIters r s < 2 ^ 31 := by
  have h1 := hpre.seqRange r hr
  have hsp := hpre.splitsPos
  unfold Params.numIters Params.blocks
  have := ceil_div_le ((Q.seqK r + 127) / 128 - s) Q.splits hsp
  omega

/-- **The epilogue skips the load exactly when the split has no block.** -/
theorem skip_of (hpre : Pre Q L mem0) (hf : Interface.ThreadFacts Q L mem0 X) (hg : g < L.threads)
    {k : Nat} {d : Epi.D} (hσ : Interface.St Q L X g k = some (some (.d (.epi d)))) :
    d.sk = true ↔ Q.numIters (reqOf L g) (splitOf L g) = 0 := by
  obtain ⟨k1, dsm, d1, h1, h2, -, h4, h5⟩ := epi_origin k d hσ
  have hm : Interface.SmMeans Q L g dsm.e := (hf.reach hg h1).2
  have hr25 : dsm.e.r25 = Q.numIters (reqOf L g) (splitOf L g) := hm.ent.r25
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hlt := numIters_lt hpre (r := reqOf L g) hz (splitOf L g)
  rw [← h4]
  have hsk : (DComp.exitIn L g dsm).skip = decide (Q.numIters (reqOf L g) (splitOf L g) < 1) := by
    show decide (toSigned 32 (BitVec.ofNat 64 dsm.e.r25) < 1) = _
    rw [hr25]
    unfold toSigned
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [show Q.numIters (reqOf L g) (splitOf L g) < 2 ^ (32 - 1) from hlt, ↓reduceIte]
    simp only [decide_eq_decide]
    omega
  rw [h5]
  by_cases h0 : Q.numIters (reqOf L g) (splitOf L g) = 0
  · have hs : (DComp.exitIn L g dsm).skip = true := by rw [hsk]; simp [h0]
    simp only [hs, ↓reduceIte]
    exact ⟨fun _ => h0, fun _ => rfl⟩
  · have hs : (DComp.exitIn L g dsm).skip = false := by rw [hsk]; simp; omega
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h => absurd h (by simp [Epi.D.start, Epi.D.entry]), fun h => absurd h h0⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
