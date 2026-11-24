-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvInitialAccumulator
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QkAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadbackOrder
import Lemmas.Tcgen05.TcProgramOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCellWriters
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader

@[expose] public section

/-! # Tensor-memory writes agree on their region and have a cell-local order -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem pv_rescale_order {g i t j : Nat} {d : Wg1Mma.D} {k : Fin 8} {r : Fin 4} {q : Wg0.D}
    {cell : TcMma.Cell} (hi : PvAccumulatorSource.Issue L X g i d.i k)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) (hsite : d.site = .pvMma k)
    (hstore : PvAccumulatorSource.RescaleStore P L X t j cell q r) (hcta : ctaOf L t = ctaOf L g) :
    TcMma.WriteBefore L X (g, i) (t, j) ∨ TcMma.WriteBefore L X (t, j) (g, i) := by
  by_cases h : q.block ≤ d.i
  · exact .inr (PvAccumulatorSource.earlier_rescale hpre hX hs ht hi hd hsite hstore hcta h)
  · exact .inl (.inl (.inl
      (PvAccumulatorSource.later_rescale hpre hX hs ht hi hd hsite hstore hcta (by omega))))

private theorem output_writes_ordered {g i t j : Nat} {cell : TcMma.Cell} (hcol : cell.column < 256)
    (hi : TcMma.TmemWrite L X (g, i) cell) (hj : TcMma.TmemWrite L X (t, j) cell) :
    (g, i) = (t, j) ∨ TcMma.WriteBefore L X (g, i) (t, j) ∨
      TcMma.WriteBefore L X (t, j) (g, i) := by
  obtain ⟨hc, hwi⟩ := PvAccumulatorSource.output_writer hpre hX hs ht hcol hi
  obtain ⟨hc', hwj⟩ := PvAccumulatorSource.output_writer hpre hX hs ht hcol hj
  rcases hwi with ⟨d, k, hd, hsite, hmma, hhalf⟩ | ⟨d, k, hstore⟩
  · rcases hwj with ⟨d', k', hd', hsite', hmma', hhalf'⟩ | ⟨d', k', hstore'⟩
    · obtain ⟨_, hu⟩ := GemmRing.exists_issuer (cta := cell.cta) hpre hX
        (fun a ha => (hs a ha).machine)
      have heq := (hu g i d hc.symm hd (by rw [hsite]; simp)).trans
        (hu t j d' hc'.symm hd' (by rw [hsite']; simp)).symm
      subst t
      rcases Nat.lt_trichotomy i j with h | rfl | h
      · exact .inr (.inl (.inl
          (PvAccumulatorSource.pv_before hX hmma hmma' h (hhalf.symm.trans hhalf'))))
      · exact .inl rfl
      · exact .inr (.inr (.inl
          (PvAccumulatorSource.pv_before hX hmma' hmma h (hhalf'.symm.trans hhalf))))
    · exact .inr (pv_rescale_order hpre hX hs ht hmma hd hsite hstore' (hc'.symm.trans hc))
  · rcases hwj with ⟨d', k', hd', hsite', hmma', _⟩ | ⟨d', k', hstore'⟩
    · rcases pv_rescale_order hpre hX hs ht hmma' hd' hsite' hstore (hc.symm.trans hc') with h | h
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    · obtain ⟨rfl, _⟩ := PvInitialAccumulator.same_rescale_lane hpre hX hs hstore hstore'
      rcases Nat.lt_trichotomy i j with h | rfl | h
      · exact .inr (.inl (.inr (.inl (TcMma.StoreDoneBefore.of_po hstore.store hstore'.store
          (Frame.lt_of_get hX hstore.store.choose_spec) rfl h))))
      · exact .inl rfl
      · exact .inr (.inr (.inr (.inl (TcMma.StoreDoneBefore.of_po hstore'.store hstore.store
          (Frame.lt_of_get hX hstore'.store.choose_spec) rfl h))))

/-- The unique query copy and the ordered QK, PV and rescale chains cover every written cell. -/
theorem no_tmem_writes_unsafe :
    ¬ TcMma.WritesUnsafe L X := by
  intro hunsafe
  apply hunsafe
  rintro ⟨g, i⟩ ⟨t, j⟩ cell hi hj
  by_cases hlo : cell.column < 256
  · exact output_writes_ordered hpre hX hs ht hlo hi hj
  by_cases hhi : cell.column < 400
  · have hcol : 256 ≤ cell.column ∧ cell.column < 400 := ⟨by omega, hhi⟩
    obtain ⟨d, ei, k, hget, hcta, hd, hsite, hmin, hmax⟩ :=
      QueryCellWriters.copy_writer_of_column hpre hX hs hcol hi
    obtain ⟨d', ej, k', hget', hcta', hd', hsite', hmin', hmax'⟩ :=
      QueryCellWriters.copy_writer_of_column hpre hX hs hcol hj
    have hk : k = k' := by
      apply Fin.ext
      unfold Wg1Mma.qkACol Wg1Mma.tmemQ at hmin hmax hmin' hmax'
      omega
    subst k'
    obtain ⟨_, hu⟩ := GemmRing.exists_issuer (cta := cell.cta) hpre hX
      (fun a ha => (hs a ha).machine)
    have heq := (hu g i d hcta hd (by rw [hsite]; simp)).trans
      (hu t j d' hcta' hd' (by rw [hsite']; simp)).symm
    subst t
    obtain rfl := QueryTmaSites.copy_site_unique hget hget' hd hd' hsite hsite'
    exact .inl rfl
  · obtain ⟨lane, hu⟩ := Wg1MmaLeader.cta_issuer (cta := cell.cta) hpre hX
      (fun a ha => (hs a ha).machine)
    let issuer := cell.cta * L.block + 128 + lane.val
    have hcta : cell.cta = ctaOf L issuer := by
      simp only [issuer, ctaOf, hpre.block]
      have := lane.isLt
      omega
    have hu' : GemmRing.MmaIssuer P L X (ctaOf L issuer) issuer := hcta ▸ hu
    obtain ⟨rfl, _, _, hmma⟩ :=
      QkAccumulatorSource.issue_of_write hpre hX hs hu' hcta (by omega) hi
    obtain ⟨rfl, _, _, hmma'⟩ :=
      QkAccumulatorSource.issue_of_write hpre hX hs hu' hcta (by omega) hj
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · exact .inr (.inl (ScoreReadback.earlier_qk_write hX hmma hmma' h))
    · exact .inl rfl
    · exact .inr (.inr (ScoreReadback.earlier_qk_write hX hmma' hmma h))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
