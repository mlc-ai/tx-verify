-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Ordered
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Cells
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds

@[expose] public section

/-! # The sources of the Tensor Memory loads

A Tensor Memory load is a consumer's load of sixteen words of its warp group's buffer
(`ThreadFacts.tc_coll`, `ld_len`), in the tile numbered by its arrivals on the buffer's empty
barrier (`ThreadFacts.cons_load`). The only writers of its cells are the MMAs of the buffer's
producer (`writer_producer`). Its source is the producer's last MMA of a batch up to the load's tile
(`load_source`): such an MMA exists, as the consumer's full poll observed a commit notification
and the producer's first accumulator commit follows an MMA (`first_mma`). The accumulator ring's
order (`TmemOrdered`) makes the source complete before the load, the producer's earlier MMAs are
pipelined before it, and its later ones follow the load's wait. The source's value is the completed
MMA's result (`TcMma.CompletedValues`), and allocation and release follow the accesses' lifetimes
(`TmemLive`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier TcMma

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An MMA of the kernel: an MMA thread's, of the operands `mmaSpec`, at its warp's buffer. -/
theorem mma_shape (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    (i.1 % L.block / 32 = 8 ∨ i.1 % L.block / 32 = 9) ∧ i.1 / L.block % 2 = 0 ∧
      d = 256 * (i.1 % L.block / 32 % 2) ∧ mask = List.replicate 8 0 ∧
      ∃ sl j : Nat, s = InputRing.mmaSpec L (i.1 / L.block) (i.1 % L.block / 32) sl j := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX he
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨hw, hlead, -⟩ := ht.mma_acc_batch hg he hσ rfl
  obtain ⟨hd, hm⟩ := ht.mma_dst hg he hσ rfl
  exact ⟨hw, hlead, hd, hm, mma_spec hX ht ⟨pc, he⟩⟩

/-- **The writers of a buffer's cell are its producer's MMAs.** An MMA writing a cell of CTA
`2 c` or `2 c + 1` at a column of buffer `j` is the producer's. -/
theorem writer_producer (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {c : Nat} {j : Fin 2} {i : EvId} {cell : Cell} (hc : X.MmaCell i cell)
    (hcta : cell.cta / 2 = c) (hcol : cell.column / 256 = j.val) :
    i.1 = producer L X c j ∧ ∃ d s acc mask, X.MmaIssue i d s acc mask ∧
      d = 256 * j.val ∧ mask = List.replicate 8 0 ∧
      ∃ sl jj : Nat, s = InputRing.mmaSpec L (2 * c) (8 + j.val) sl jj := by
  obtain ⟨d, s, acc, mask, row, col, hi, hw⟩ := hc
  obtain ⟨hw89, hlead, rfl, rfl, sl, jj, rfl⟩ := mma_shape hX ht hi
  obtain ⟨hr, hcl, rfl⟩ := writeCell_mma hw
  simp only at hcta hcol
  have hj := j.isLt
  have hgc : i.1 / L.block = 2 * c := by omega
  have hgw : i.1 % L.block / 32 = 8 + j.val := by omega
  have hprod : producerThread L c j i.1 = true := by
    simp only [producerThread, decide_eq_true_eq]
    exact ⟨hgc, hgw⟩
  obtain ⟨pc, he⟩ := hi
  obtain ⟨g, k⟩ := i
  simp only at hgc hgw hprod hw89 hlead ⊢
  have hg := Frame.lt_of_get hX he
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨-, -, hbatch⟩ := ht.mma_acc_batch hg he hσ rfl
  obtain ⟨jp, pcp, pp, acqp, scp, -, hep⟩ := exists_okPoll (X := X) (g := g) (k := k)
    (m := Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, false⟩) (by omega)
  have hempty : Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, false⟩ =
      (slot L c j).empty 0 := by
    simp only [slot, hgc]
    congr 2
    omega
  rw [hempty] at hep
  refine ⟨producer_eq hX ht hprod hep, _, _, acc, _, ⟨pc, he⟩, by omega, rfl, sl, jj, ?_⟩
  rw [hgc, hgw]

/-- **The producer has an MMA before its first accumulator commit**, once a consumer has polled
its full barrier successfully: the poll observed a commit notification of the producer, and an
accumulator commit follows an MMA of its thread. -/
theorem first_mma (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {jw pc p : Nat} {acq : Bool}
    {sc : MbarScope}
    (hew : X.get (consumerOf L c j b, jw) =
      some ⟨pc, .wait ((slot L c j).full ((slot L c j).owner b)) p true acq sc⟩) :
    ∃ k0 pc0 d0 s0 a0 m0, X.get (producer L X c j, k0) = some ⟨pc0, .tc (.mma d0 s0 a0 m0)⟩ ∧
      ((X.tr (producer L X c j)).take k0).countP (commitsTo ((slot L c j).full 0)) = 0 := by
  classical
  obtain ⟨jr, r, -, -, -, -, -, hfl⟩ := cons_poll hpre hX ht hew
  have hpos : 0 < ((X.objects ((slot L c j).full ((slot L c j).owner b))).take jr).countP
      isArrival := by omega
  obtain ⟨x, hxm, hxn⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨jc, pcc, spc, -, hcm, hmb, -⟩ := notify_commit hpre hX ht (List.mem_of_mem_take hxm) hxn
  have hex : ∃ i, ∃ pc sp, X.get (producer L X c j, i) = some ⟨pc, .tc (.commit sp)⟩ ∧
      sp.mbar = (slot L c j).full 0 := ⟨jc, pcc, spc, hcm, hmb⟩
  obtain ⟨pc1, sp1, he1, hm1⟩ := Nat.find_spec hex
  have hmin := fun i (hi : i < Nat.find hex) => Nat.find_min hex hi
  have hP := producer_thread (X := X) hpre c j
  simp only [producerThread, decide_eq_true_eq] at hP
  have hg := Frame.lt_of_get hX he1
  obtain ⟨d1, hσ1⟩ := Frame.event_state ht.sound hX ht.tracked he1 (by simp)
  have hj := j.isLt
  obtain ⟨k0, pc0, d0, s0, a0, m0, hk0, he0⟩ := ht.acc_commit_mma hg he1 hσ1 rfl (by
    rw [hm1]
    simp only [slot, Fin.val_zero, Nat.add_zero, hP.1]
    congr 2
    omega)
  refine ⟨k0, pc0, d0, s0, a0, m0, he0, ?_⟩
  rw [List.countP_eq_zero]
  intro e hmem hce
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hmem
  rw [List.length_take] at hi
  have hget : X.get (producer L X c j, i) = some e := by
    show (X.tr _)[i]? = some e
    rw [← hgi, List.getElem?_eq_getElem (by simp only; omega), List.getElem_take]
  obtain ⟨pce, kd⟩ := e
  unfold commitsTo at hce
  split at hce
  · rename_i sp hkd
    simp only at hkd
    subst hkd
    exact hmin i (by omega) ⟨pce, sp, hget, of_decide_eq_true hce⟩
  · cases hce

/-- The cell of word `j` of a consumer's load of chunk `ch` of its buffer. -/
theorem load_cell {h ch j : Nat} (hw : h % L.block / 32 < 8) (hch : ch < 16) :
    tcDataCell32 L h (256 * (h % L.block / 32 / 4) + 16 * ch) j =
      ⟨h / L.block, h % L.block % 128, 256 * (h % L.block / 32 / 4) + 16 * ch + j⟩ := by
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq, true_and]
  constructor
  · omega
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- **The source of a Tensor Memory load's word**: the producer's last MMA of a batch up to the
load's tile. -/
theorem load_source (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hins : InstructionSafe L Prod X) (hlive : TmemLive L X)
    {e : EvId} {j : Nat} {cl : Cell} (hlc0 : LoadCell L X e j cl) :
    ∃ source value, ReadSource L X .ld source e cl ∧ Wrote L Prod X source cl value := by
  classical
  have hblock := hpre.block
  have hord := tmemOrdered hpre hX ht
  obtain ⟨h, k'⟩ := e
  obtain ⟨a, vals, sh, ⟨pcl, hel⟩, hj, hcl⟩ := hlc0
  have hh := Frame.lt_of_get hX hel
  obtain rfl := ht.ld_shape hh hel
  have hlen := ht.ld_len hh hel
  obtain ⟨hw8, p, -, hkind, -⟩ := ht.tc_coll hh hel rfl
  obtain ⟨ch, hch, rfl⟩ : ∃ ch, ch < 16 ∧ a = 256 * (h % L.block / 32 / 4) + 16 * ch := by
    unfold TcCollKind at hkind
    split_ifs at hkind
    · obtain ⟨v, hv⟩ := hkind
      simp only [TcKind.ld.injEq] at hv
      exact ⟨p / 2, by omega, hv.1⟩
    all_goals exfalso; simp_all
  obtain ⟨dl, hσl⟩ := Frame.event_state ht.sound hX ht.tracked hel (by simp)
  obtain ⟨-, htile, -⟩ := ht.cons_load hh hel hσl
  set c := h / L.block / 2 with hc
  set jb : Fin 2 := ⟨h % L.block / 32 / 4, by omega⟩ with hjb
  set b : Fin 256 := ⟨(h / L.block - 2 * c) * 128 + h % L.block % 128, by omega⟩ with hbdef
  have hb : consumerOf L c jb b = h := consumerOf_of rfl rfl
  set q := arrivals (Bar.loc L (2 * (h / L.block / 2)) ⟨.acc, h % L.block / 32 / 4, false⟩)
    ((X.tr h).take k') with hq
  have hfull' : Bar.loc L (h / L.block) ⟨.acc, h % L.block / 32 / 4, true⟩ =
      (slot L c jb).full ((slot L c jb).owner b) := by
    have hcta : 2 * c + b.val / 128 = h / L.block := by simp only [hbdef]; omega
    show _ = Bar.loc L (2 * c + b.val / 128) ⟨.acc, jb.val, true⟩
    rw [hcta]
  rw [hfull'] at htile
  obtain ⟨jw, pcw, pw, acqw, scw, -, hew, -⟩ := MbarRing.Poll.exists_nth (X := X) (g := h)
    (k := k') (m := (slot L c jb).full ((slot L c jb).owner b)) (n := q) (by omega)
  rw [← hb] at hew
  obtain ⟨k0, pc0, d0, s0, a0, m0, he0, hc0⟩ := first_mma hpre hX ht hew
  have hP := producer_thread (X := X) hpre c jb
  simp only [producerThread, decide_eq_true_eq] at hP
  set Pr := producer L X c jb with hPr
  have hfullP : Bar.loc L (Pr / L.block) ⟨.acc, Pr % L.block / 32 % 2, true⟩ =
      (slot L c jb).full 0 := by
    simp only [slot, Fin.val_zero, Nat.add_zero, hP.1]
    congr 2
    omega
  -- the source: the producer's last MMA of a batch up to the load's tile
  let Q : Nat → Prop := fun i => ∃ pc d s acc mask,
    X.get (Pr, i) = some ⟨pc, .tc (.mma d s acc mask)⟩ ∧
      ((X.tr Pr).take i).countP (commitsTo ((slot L c jb).full 0)) ≤ q
  have hQ0 : Q k0 := ⟨_, _, _, _, _, he0, by omega⟩
  have hlenP : ∀ i, Q i → i ≤ (X.tr Pr).length := fun i ⟨_, _, _, _, _, he, _⟩ => idx_le he
  have hQs : Q (Nat.findGreatest Q (X.tr Pr).length) := Nat.findGreatest_spec (hlenP k0 hQ0) hQ0
  have hmax : ∀ i, Q i → i ≤ Nat.findGreatest Q (X.tr Pr).length :=
    fun i hi => Nat.le_findGreatest (hlenP i hi) hi
  set ks := Nat.findGreatest Q (X.tr Pr).length
  obtain ⟨pcs, ds, ss, accs, masks, hes, hbs⟩ := hQs
  have hiss : X.MmaIssue (Pr, ks) ds ss accs masks := ⟨pcs, hes⟩
  obtain ⟨-, -, rfl, rfl, sl, jj, rfl⟩ := mma_shape hX ht hiss
  have hjv : jb.val = h % L.block / 32 / 4 := rfl
  have hc1 : h / L.block / 2 = Pr / L.block / 2 := by omega
  have hc2 : h % L.block / 32 / 4 = Pr % L.block / 32 % 2 := by omega
  have hdone : DoneBefore L X (Pr, ks) (h, k') :=
    (hord Pr ks h k' _ _ _ _ _ _ _ hiss ⟨pcl, hel⟩ hc1 hc2).1 (by rw [hfullP]; exact hbs)
  -- the cell
  have hcell := load_cell (L := L) (j := j) hw8 hch
  set cell := tcDataCell32 L h (256 * (h % L.block / 32 / 4) + 16 * ch) j
  have hmc : X.MmaCell (Pr, ks) cell := by
    refine ⟨_, _, _, _, b.val, 16 * ch + j, hiss, ?_⟩
    rw [writeCell_mma_of b.isLt (by omega), hcell]
    simp only [Option.some.injEq, Cell.mk.injEq, hbdef]
    refine ⟨by omega, by omega, by omega⟩
  obtain ⟨value, hres⟩ :=
    (hins.1 _ _ _ _ _ hiss).2 (hdone.done hX.tcCommit) cell hmc
  have hcl' : cl = cell := by rw [hcl, tcDataCell_s32x32b]
  rw [hcl'] at hcl ⊢
  have hlc : LoadCell L X (h, k') j cell := ⟨_, vals, _, ⟨pcl, hel⟩, hj, hcl⟩
  have hll := hlive (h, k') cell (.inr (.inl ⟨j, hlc⟩))
  have hne : (Pr, ks) ≠ (h, k') := by
    intro heq
    rw [heq, hel] at hes
    cases hes
  refine ⟨(Pr, ks), value, ⟨hne, .inl hmc, .inl (.inl hdone), ?_, ?_⟩, .inl hres⟩
  · -- every other writer of the cell is the producer's MMA, before the source or after the load
    intro other hwr
    rcases hwr with hm | ⟨a', vs, sh', jj', ⟨pc', hst⟩, -⟩ | ⟨c', cta, idx, ln, ⟨pc', hcp⟩, -⟩ |
      ⟨s', hsh, -⟩
    · obtain ⟨hoP, -⟩ := writer_producer hX ht hm (j := jb) (by rw [hcell]) (by
        rw [hcell]; simp only; omega)
      obtain ⟨g', k''⟩ := other
      simp only at hoP
      subst hoP
      obtain ⟨d', s', acc', mask', row', col', hi', -⟩ := hm
      obtain ⟨pc'', he''⟩ := hi'
      obtain ⟨-, -, rfl, rfl, sl', jj', rfl⟩ := mma_shape hX ht ⟨pc'', he''⟩
      by_cases hle : ((X.tr Pr).take k'').countP (commitsTo ((slot L c jb).full 0)) ≤ q
      · rcases Nat.lt_or_eq_of_le (hmax k'' ⟨_, _, _, _, _, he'', hle⟩) with hlt | heq
        · have hPl := Frame.lt_of_get hX hes
          refine .inr (.inl (.inl (.inr ⟨⟨⟨hPl, hPl, rfl⟩, rfl⟩,
            .inl (.single (.inl (po_of_source_not_access rfl hlt (len_of_get hes)
            (by simp [he'', Event.acc])))), _, _, _, _,
            _, _, _, _, ⟨pc'', he''⟩, hiss, rfl, rfl, rfl, rfl, rfl⟩)))
        · exact .inl (by rw [heq])
      · refine .inr (.inr (.inl ((hord Pr k'' h k' _ _ _ _ _ _ _ ⟨pc'', he''⟩ ⟨pcl, hel⟩ hc1
          hc2).2 ?_)))
        rw [hfullP]
        omega
    · have hg := Frame.lt_of_get hX hst
      obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hst (by simp)
      exact absurd rfl (ht.no_tc_st hg hst hσ)
    · have hg := Frame.lt_of_get hX hcp
      obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hcp (by simp)
      exact absurd rfl (ht.no_tc_cp hg hcp hσ)
    · exact (Safety.no_shift hX ht hsh).elim
  · intro key r hr hcov rel hrel
    exact .inl (hll.2 key r hr hcov rel hrel)

/-- **Every register of every Tensor Memory load has a source** (the load clause of
`TcMma.SourceSafe`). -/
theorem loadSources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hins : InstructionSafe L Prod X) (hlive : TmemLive L X) :
    ∀ e j cell, LoadCell L X e j cell →
      ∃ source value, ReadSource L X .ld source e cell ∧ Wrote L Prod X source cell value :=
  fun _ _ _ hlc => load_source hpre hX ht hins hlive hlc

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
