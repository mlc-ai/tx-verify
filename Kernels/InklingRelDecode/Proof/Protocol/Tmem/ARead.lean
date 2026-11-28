-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkPv
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PstDone
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreMma
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BlockCounts
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # A PV MMA's read of the probabilities is ordered with every writer of its cells

The PV MMA of block `m` (state `b = m + 1`) reads the first 64 columns of the score buffer of parity
`m % 2`, eight columns at a time. Its writers are the QK MMAs and the probability stores of that
buffer: those of blocks (rounds) at most `m` are done before it, the others are after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A QK MMA of an earlier block of the same buffer is written before a PV MMA's A read.** -/
public theorem qk_wb_pv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (words : RoleBytes L X) {g kp kq pc pcw dst dw b b2 : Nat} {s sw : OperandSpec} {acc aw : Bool}
    {mask mw : List Nat}
    (hg : g < L.threads) (he : X.get (g,kp) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (gw : X.get (g,kq) = some ⟨pcw,.tc (.mma dw sw aw mw)⟩)
    (hq : ∃ j : Fin 8, pcw = Lib.qkIssue j) (pb : pollRound 2510 ((X.tr g).take kp) = b)
    (one : 1 ≤ b) (q1 : pollRound 2462 ((X.tr g).take kq) = b2+1)
    (warp2 : g%L.block/32 = 7) (par : b2%2 = (b-1)%2) (early : b2 < b) :
    WriteBefore L X (g,kq) (g,kp) := by
  refine WriteBefore.of_done ?_
  have few := qk_commits_before hp hX hf rows words (c := g/L.block)
    (s := MbarRow.slot2 (b-1)) hg gw (by
      obtain ⟨j0,rfl⟩ := hq
      fin_cases j0 <;> decide) warp2 q1 (by show (b-1)%2 = b2%2; omega)
  exact qk_before_pv hp hX hf rows init words gw he pb one (by omega)

/-- **A PV MMA's A read and a writer of its cells are ordered.** -/
public theorem a_read_order (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {r w : EvId} {cell : Cell}
    (hr : X.MmaACell r cell) (hw : TmemWrite L X w cell) :
    r = w ∨ WriteBefore L X w r ∨ ReadBefore L X .a r w := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨g,kp⟩ := r
  obtain ⟨d,s,acc,mask,index,b0,⟨pc,he⟩,hac⟩ := id hr
  obtain ⟨-,lo,hi,b',qk|pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j,-,-,none,-⟩ := qk
    simp [aCell,none] at hac
  obtain ⟨j,hpcj,-,-,-⟩ := pv
  obtain ⟨b,-,pb,one,p2462,⟨j',hat⟩,warp,-⟩ := Mma.Export.pv_block hp hX hf base he ⟨j,hpcj⟩
  obtain ⟨hcta,hlo,hhi⟩ := mma_a_range hp hX hf base he hat hr
  simp only at hcta
  have hg := Frame.lt_of_get hX he
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : g/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 hg
  have hj8 := j'.isLt
  have lent : kp < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases tmemWrite_of_no_copy (Lib.no_cp hX) (no_shift hX) hw with hm | hs
  · obtain ⟨pcw,dw,sw,aw,mw,gw,cw,l1,h1,-,-,kw⟩ := mma_write_cell hp hX hf base hm
    obtain ⟨gq,kq⟩ := w
    simp only at cw
    rcases kw with ⟨jq,hpq,hdq,-⟩ | ⟨-,-,hd,-⟩
    · obtain ⟨b2,hd2,q1,q2,warp2,-⟩ := Mma.Export.qk_block hp hX hf base gw ⟨jq,hpq⟩
      have cta : gq/L.block = g/L.block := by rw [← cw, hcta]
      have thr : g = gq := (mma_thread hp hX hf he gw cta.symm)
      subst thr
      have par : b2%2 = (b-1)%2 := by omega
      rcases Nat.lt_or_ge b2 b with early | late
      · exact .inr (.inl (qk_wb_pv hp hX hf rows init words hg he gw ⟨jq,hpq⟩ pb one q1 warp2
          (by omega) early))
      · refine .inr (.inr (.inr (.inr (.inl ?_))))
        have lt : kp < kq := by
          by_contra! le
          have ne : kq ≠ kp := by
            rintro rfl
            rw [gw] at he
            simp only [Option.some.injEq, Event.mk.injEq] at he
            obtain ⟨rfl,-⟩ := he
            have : Lib.qkIssue jq = Lib.pvIssue j := hpq.symm.trans hpcj
            revert this; fin_cases jq <;> fin_cases j <;> decide
          have mono := countP_take_mono (okPollAt 2462) (X.tr g) le
          change pollRound 2462 _ ≤ pollRound 2462 _ at mono
          omega
        exact Pipelined.of_aRead_po ⟨pc,he⟩ (by rw [hat]; rfl) ⟨pcw,gw⟩ hg rfl lt
    · omega
  · obtain ⟨gq,kq⟩ := w
    obtain ⟨lt,tt,kw⟩ := st_write_cell hp hX hf base hs
    simp only at lt tt
    rcases kw with ⟨a,vals,ba,wd,jj,hy,rfl,hb,hj,hc'⟩ | ⟨a,vals,wd,jj,hy,rfl,hj,hc'⟩
    · obtain ⟨c1,c2,c3⟩ := p_cols (L := L) (g := gq) (w := wd) hb hj
      simp only at hc'
      rw [← hc'] at c1 c2 c3
      have cta : gq/L.block = g/L.block := by
        obtain ⟨-,hs2⟩ := hs
        rw [← c3, hcta]
      have tc : isTcColl ⟨1009,.tc (.st (ba+wd*2^21) vals (.s16x32bx2 32))⟩ = true := rfl
      obtain ⟨rs,wst,s1,-,s3,sta⟩ := Export.st_round hp hX hf base hy tc (.inl rfl)
      have haddr := pst_address sta
      have par : rs%2 = (b-1)%2 := by omega
      simp only [ite_true] at s3
      rcases Nat.lt_or_ge rs b with early | late
      · refine .inr (.inl (.inr (.inl ?_)))
        have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 rs)) kp
        change okPolls ((Object.prob (MbarRow.slot2 rs)).loc L (g/L.block)) ((X.tr g).take kp) =
          (Object.prob (MbarRow.slot2 rs)).visits (pollRound 2510 ((X.tr g).take kp)) at cnt
        rw [pb] at cnt
        have vis : (Object.prob (MbarRow.slot2 rs)).visits b = (b+2-1-rs%2)/2 := rfl
        obtain ⟨lead,-⟩ := mma_leader hp hX hf he
        simp only at lead
        have := store_before_mma hp hX hf safe base rows init words hc hy (.inl rfl) lt
          cta s1 (k := kp) (by rw [lead]; exact lent) (by rw [lead,cnt,vis]; omega)
        rw [lead] at this
        exact this
      · refine .inr (.inr (.inr (.inl ?_)))
        have few := pv_scores_before hp hX hf rows words (c := g/L.block)
          (s := MbarRow.slot2 rs) hg warp p2462 (by show rs%2 = (b-1)%2; omega)
        exact mma_before_pst hp hX hf safe rows init words he hy lt cta.symm s1 s3 (by omega)
    · obtain ⟨c1,c2,c3⟩ := o_cols (L := L) (g := gq) (w := wd) hj
      simp only at hc'
      rw [← hc'] at c1 c2 c3
      omega

end PTX.Kernels.InklingRelDecode.Proof.Tmem
