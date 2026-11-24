-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Sources
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.MmaExit
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Order

@[expose] public section

/-! # A Tensor Memory load reads its tile's last MMA

A consumer's load of tile `q` (its arrivals on the buffer's empty barrier) follows its `q + 1`-th
successful poll of the buffer's full barrier, which observed `q + 1` notifications of distinct
accumulator commits of the producer (`cons_poll`, `notify_commit`). So the producer made its
accumulator commit numbered `q`, and two events before it the MMA that ends task `q`
(`ThreadFacts.acc_commit_last`). That MMA is the source of every word of the load
(`load_last`): it is the producer's last MMA with at most `q` accumulator commits before it, which
`TmemOrdered` orders before the load, the earlier ones are pipelined before it, and the later ones
follow the load. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier TcMma

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The source of a Tensor Memory load's word is its tile's last MMA**: two events before the
producer's accumulator commit numbered by the load's tile. -/
theorem load_last (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hins : InstructionSafe L Prod X) (hlive : TmemLive L X)
    {h k' a : Nat} {vals : List Value} {sh : TcShape} (hld : X.TLd (h, k') a vals sh)
    {j : Nat}
    (hj : j < vals.length) :
    ∃ g jc m pcm dst sp acc mask cell value, g < L.threads ∧
      g / L.block = 2 * (h / L.block / 2) ∧ g % L.block / 32 = 8 + h % L.block / 32 / 4 ∧
      jc ≤ (X.tr g).length ∧ Frame.stateAt (code L) X g jc = some (some (.inr (.mma m))) ∧
      m.site = .accCommit ∧
      ((X.tr g).take jc).countP
          (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
        arrivals (Bar.loc L (2 * (h / L.block / 2)) ⟨.acc, h % L.block / 32 / 4, false⟩)
          ((X.tr h).take k') ∧
      X.get (g, jc - 2) = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      writeCell sp dst mask (128 * (h / L.block % 2) + h % L.block % 128)
        (a - 256 * (h % L.block / 32 / 4) + j) = some cell ∧
      X.async.mmaDone (g, jc - 2) = true ∧
      LoadCell L X (h, k') j cell ∧ ReadSource L X .ld (g, jc - 2) (h, k') cell ∧
      Wrote L Prod X (g, jc - 2) cell value := by
  classical
  have hblock := hpre.block
  have hord := tmemOrdered hpre hX ht
  obtain ⟨pcl, hel⟩ := hld
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
  obtain ⟨jw, pcw, pw, acqw, scw, -, hew, hcw⟩ := MbarRing.Poll.exists_nth (X := X) (g := h)
    (k := k')
    (m := (slot L c jb).full ((slot L c jb).owner b)) (n := q) (by omega)
  rw [← hb] at hew hcw
  have hP := producer_thread (X := X) hpre c jb
  simp only [producerThread, decide_eq_true_eq] at hP
  set Pr := producer L X c jb with hPr
  have hPl : Pr < L.threads := by
    have h1 := hP.1
    rw [hblock] at h1
    simp only [Launch.threads, hpre.grid, hblock, hc] at hh h1 ⊢
    omega
  -- the producer made `q + 1` accumulator commits
  set F := (slot L c jb).full ((slot L c jb).owner b) with hF
  obtain ⟨jr, r, -, -, -, -, -, hfl⟩ := cons_poll hpre hX ht hew
  rw [hcw] at hfl
  have hnd : (X.objects F).Nodup := List.Nodup.of_map _ (hX.tma.2.2.1 F).1.1
  have hNnd : (((X.objects F).take jr).filter isArrival).Nodup :=
    (hnd.sublist (List.take_sublist _ _)).filter _
  let f : Record Ref → Nat := fun x => match x.id with
    | .async i _ => i.2
    | _ => 0
  have hcnt := MbarRing.Slot.length_le_countP_take _ hNnd (X.tr Pr)
    (commitsTo ((slot L c jb).full 0)) (X.tr Pr).length f ?_ ?_
  rotate_left
  · intro x hx
    obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
    obtain ⟨jc, pcc, sp, hid, hcm, hmb, -⟩ :=
      notify_commit hpre hX ht (List.mem_of_mem_take hxt) hxn
    have hfx : f x = jc := by simp only [f, hid]
    rw [hfx]
    refine ⟨(List.getElem?_eq_some_iff.mp hcm).1, ?_⟩
    change (X.get (producer L X c jb, jc)).any _ = true
    rw [hcm]
    simp [commitsTo, hmb]
  · intro x hx y hy hxy
    obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
    obtain ⟨hyt, hyn⟩ := List.mem_filter.mp hy
    obtain ⟨jc, -, -, hid, -⟩ := notify_commit hpre hX ht (List.mem_of_mem_take hxt) hxn
    obtain ⟨jc', -, -, hid', -⟩ := notify_commit hpre hX ht (List.mem_of_mem_take hyt) hyn
    have h1 : f x = jc := by simp only [f, hid]
    have h2 : f y = jc' := by simp only [f, hid']
    rw [h1, h2] at hxy
    subst hxy
    exact hX.record_eq (List.mem_of_mem_take hxt) (List.mem_of_mem_take hyt) (hid.trans hid'.symm)
  rw [List.take_length, ← List.countP_eq_length_filter] at hcnt
  obtain ⟨jc, xc, hxc, hxcp, hcjc⟩ := MbarRing.Slot.exists_nth_countP
    (commitsTo ((slot L c jb).full 0)) (xs := X.tr Pr) (c := q) (by rw [hF] at hcnt; omega)
  obtain ⟨spc, hkc, hmbc⟩ := InputRing.commitsTo_form hxcp
  have hjcl : jc < (X.tr Pr).length := (List.getElem?_eq_some_iff.mp hxc).1
  obtain ⟨dc, hσc⟩ := Frame.event_state ht.sound hX ht.tracked hxc (by rintro pc f rfl; cases hkc)
  obtain ⟨mc, rfl, -, hcs⟩ := ht.commit_spec hPl hxc hσc hkc
  have hfullP : Bar.loc L (Pr / L.block) ⟨.acc, Pr % L.block / 32 % 2, true⟩ =
      (slot L c jb).full 0 := by
    simp only [slot, Fin.val_zero, Nat.add_zero, hP.1]
    congr 2
    omega
  have hacs : mc.site = .accCommit := by
    rcases hcs with ⟨s, -, hsp⟩ | ⟨hs, -⟩
    · exfalso
      rw [hsp] at hmbc
      simp only [slot, Bar.loc, Bar.off, Fin.val_zero, Nat.add_zero, Loc.mk.injEq] at hmbc
      have := s.isLt
      omega
    · exact hs
  obtain ⟨hj2, -, ⟨pcm, dst, sp, acc, mask, hem⟩, ⟨pcc1, spc1, hec1⟩, -⟩ :=
    ht.acc_commit_last hPl hjcl.le hσc hacs
  set K := jc - 2 with hK
  have hiss : X.MmaIssue (Pr, K) dst sp acc mask := ⟨pcm, hem⟩
  obtain ⟨-, -, rfl, rfl, sl, jj, rfl⟩ := mma_shape hX ht hiss
  have hjv : jb.val = h % L.block / 32 / 4 := rfl
  have hc1 : h / L.block / 2 = Pr / L.block / 2 := by omega
  have hc2 : h % L.block / 32 / 4 = Pr % L.block / 32 % 2 := by omega
  have hKq : ((X.tr Pr).take K).countP (commitsTo ((slot L c jb).full 0)) ≤ q := by
    rw [← hcjc]
    exact OutputRing.countP_take_mono _ _ (by omega)
  have hdone : DoneBefore L X (Pr, K) (h, k') :=
    (hord Pr K h k' _ _ _ _ _ _ _ hiss ⟨pcl, hel⟩ hc1 hc2).1 (by rw [hfullP]; exact hKq)
  -- the cell
  have hcell := load_cell (L := L) (j := j) hw8 hch
  set cell := tcDataCell32 L h (256 * (h % L.block / 32 / 4) + 16 * ch) j
  have hwc : writeCell (InputRing.mmaSpec L (Pr / L.block) (Pr % L.block / 32) sl jj)
      (256 * (Pr % L.block / 32 % 2)) (List.replicate 8 0) b.val (16 * ch + j) = some cell := by
    rw [writeCell_mma_of b.isLt (by omega), hcell]
    simp only [Option.some.injEq, Cell.mk.injEq, hbdef]
    refine ⟨by omega, by omega, by omega⟩
  have hmc : X.MmaCell (Pr, K) cell := ⟨_, _, _, _, b.val, 16 * ch + j, hiss, hwc⟩
  obtain ⟨value, hres⟩ :=
    (hins.1 _ _ _ _ _ hiss).2 (hdone.done hX.tcCommit) cell hmc
  have hlc : LoadCell L X (h, k') j cell := ⟨_, vals, _, ⟨pcl, hel⟩, hj, by rw [tcDataCell_s32x32b]⟩
  have hll := hlive (h, k') cell (.inr (.inl ⟨j, hlc⟩))
  have hne : (Pr, K) ≠ (h, k') := by
    intro heq
    rw [heq, hel] at hem
    cases hem
  refine ⟨Pr, jc, mc, pcm, _, _, acc, _, cell, value, hPl, by omega, by omega, hjcl.le, hσc,
    hacs, ?_, hem, ?_, hdone.done hX.tcCommit, hlc, ⟨hne, .inl hmc, .inl (.inl hdone), ?_, ?_⟩,
    .inl hres⟩
  · rw [hfullP, hcjc]
  · have hbv : b.val = 128 * (h / L.block % 2) + h % L.block % 128 := by simp only [hbdef]; omega
    rw [← hbv, show 256 * (h % L.block / 32 / 4) + 16 * ch - 256 * (h % L.block / 32 / 4) + j =
      16 * ch + j by omega]
    exact hwc
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
      · -- at most `q` commits before: at or before the task's last MMA
        have hk''K : k'' ≤ K := by
          by_contra hgt
          rcases Nat.lt_or_ge k'' (jc + 1) with h1 | h1
          · -- the two events after the last MMA are commits, not MMAs
            rcases (show k'' = jc - 1 ∨ k'' = jc by omega) with h2 | h2
            · rw [h2, hec1] at he''
              cases he''
            · have hx : X.get (Pr, jc) = some xc := hxc
              rw [h2, hx] at he''
              obtain rfl := Option.some.inj he''
              simp at hkc
          · have hm := OutputRing.countP_take_mono (commitsTo ((slot L c jb).full 0)) (X.tr Pr) h1
            rw [List.take_add_one, hxc, List.countP_append] at hm
            simp only [Option.toList_some, List.countP_singleton, hxcp, ↓reduceIte] at hm
            omega
        rcases Nat.lt_or_eq_of_le hk''K with hlt | heq
        · have hPl' := Frame.lt_of_get hX hem
          refine .inr (.inl (.inl (.inr ⟨⟨⟨hPl', hPl', rfl⟩, rfl⟩,
            .inl (.single (.inl (po_of_source_not_access rfl hlt (len_of_get hem)
              (by simp [he'', Event.acc])))),
            _, _, _, _, _, _, _, _, ⟨pc'', he''⟩, hiss, rfl, rfl, rfl, rfl, rfl⟩)))
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

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
