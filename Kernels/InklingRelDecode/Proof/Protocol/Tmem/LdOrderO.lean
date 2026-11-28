-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreMma
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BlockCounts
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaDone
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone
import Kernels.InklingRelDecode.Proof.Common.Export.EpiPoll
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Kernel.Frame
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # An accumulator load is ordered with every writer of its cells

The load of round `r` (pc 2260) and the epilogue's load (pc 2607) read the 128 accumulator columns,
64 registers per lane, as the rescale store of the same lane writes them: a cell fixes the thread,
so the loads and the stores are in program order. The PV MMAs of blocks at most `r` are done
before the load of round `r` by its polls of the done slot; the later ones follow the load's wait
through lane zero's publication. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The cell of an accumulator load's register** (the load of a round or the epilogue's). -/
public theorem ld_o_cell (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t k0 pc a vals sh j}
    (he : X.get (t,k0) = some ⟨pc,.tc (.ld a vals sh)⟩) (hpc : pc = 2260 ∨ pc = 2607)
    (hj : j < vals.length) :
    ∃ kk, kk < 4 ∧ a = 256 + kk*2^21 ∧ sh = .s16x32bx2 64 ∧ j < 64 ∧ t%L.block < 128 ∧
      tcDataCell L t sh a j = ⟨t/L.block, t%L.block/32%4*32 + laneOf L t % 16,
        256 + (if laneOf L t < 16 then 0 else 64) + j⟩ := by
  have lt := Export.tc_data_lane hp hX hf he (by rcases hpc with rfl|rfl <;> rfl)
  obtain ⟨i,kk,hk4,hpa,hsh,hlen⟩ := ld_static hp hX hf base he
  obtain ⟨-,ha⟩ : (pc = 2260 ∨ pc = 2607) ∧ a = 256 + kk*2^21 := by
    rcases hpa with ⟨rfl,h⟩ | h
    · omega
    · exact h
  subst ha hsh
  exact ⟨kk,hk4,rfl,rfl,by omega,lt,cell_split L t 256 64 kk j (by omega)⟩

/-- **An accumulator load and a store writing one of its cells are in program order.** -/
public theorem ld_o_store (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t k0 pc a vals sh j w}
    (he : X.get (t,k0) = some ⟨pc,.tc (.ld a vals sh)⟩) (hpc : pc = 2260 ∨ pc = 2607)
    (hj : j < vals.length) (hs : StoreCell L X w (tcDataCell L t sh a j)) :
    WriteBefore L X w (t,k0) ∨ ReadBefore L X .ld (t,k0) w := by
  have ht := Frame.lt_of_get hX he
  obtain ⟨kk,hk4,rfl,rfl,hj64,lt,-⟩ := ld_o_cell hp hX hf base he hpc hj
  obtain ⟨gq,kq⟩ := w
  obtain ⟨lt',tt',kw⟩ := st_write_cell hp hX hf base hs
  dsimp only at lt' tt'
  rcases kw with ⟨a',vals',ba,wd',jj,hy,ha',hb,hj',hc'⟩ | ⟨a',vals',wd',jj,hy,ha',hj',hc'⟩
  · exfalso
    obtain ⟨-,c1,-⟩ := p_cols (L := L) (g := gq) (w := wd') hb hj'
    rw [ha'] at hc'
    rw [← hc'] at c1
    rw [cell_split L t 256 64 kk j (by omega)] at c1
    dsimp only at c1
    split_ifs at c1 <;> omega
  rw [ha'] at hc'
  have c1 := congrArg Cell.cta hc'
  rw [cell_split L t 256 64 kk j (by omega),cell_split L gq 256 64 wd' jj (by omega)] at c1
  dsimp only at c1
  have same : t = gq := split_thread (L := L) (off := 64) (ba := 256) (by omega) (by omega)
    (by omega) lt lt' c1 hc'
  subst same
  have lenk : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
  have lenq : kq < (X.tr t).length := (List.getElem?_eq_some_iff.mp hy).1
  have ne : kq ≠ k0 := by
    rintro rfl
    rw [hy] at he
    simp only [Option.some.injEq, Event.mk.injEq] at he
    obtain ⟨rfl,-⟩ := he
    omega
  rcases Nat.lt_or_gt_of_ne ne with early | late
  · exact .inl (.inr (.inl ⟨⟨_,_,_,_,hy⟩,.inr (.inl ⟨TcMma.sameWarp_self ht,
      .inl (baseCausality_of_tc_po hy rfl early lenk),⟨_,_,_,_,hy⟩,⟨_,_,_,_,he⟩⟩)⟩))
  · exact .inr (.inr ⟨TcMma.sameWarp_self ht,.inl (baseCausality_of_tc_po he rfl late lenq),
      ⟨_,_,_,_,he⟩,⟨_,_,_,_,hy⟩⟩)

/-- **An accumulator load of round `r` and a PV MMA writing one of its cells are ordered.** -/
public theorem ld_o_pv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh j w}
    (he : X.get (t,k0) = some ⟨2260,.tc (.ld a vals sh)⟩) (hj : j < vals.length)
    (hm : X.MmaCell w (tcDataCell L t sh a j)) :
    WriteBefore L X w (t,k0) ∨ ReadBefore L X .ld (t,k0) w := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  have tc : isTcColl ⟨2260,.tc (.ld a vals sh)⟩ = true := rfl
  obtain ⟨r,wd,s1,s2,-,-,pos⟩ := Export.ld_round hp hX hf base he tc (.inr rfl)
  obtain ⟨kk,hk4,rfl,rfl,hj64,lt,cellEq⟩ := ld_o_cell hp hX hf base he (.inl rfl) hj
  simp at s2
  rw [cellEq] at hm
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  obtain ⟨pcw,d,s,acc,mask,gw,cw,l1,h1,-,-,kw⟩ := mma_write_cell hp hX hf base hm
  obtain ⟨gq,kq⟩ := w
  dsimp only at cw l1 h1
  rcases kw with ⟨jq,-,hd,-⟩ | ⟨jp,hpq,hd,-⟩
  · exfalso
    split_ifs at l1 h1 <;> omega
  obtain ⟨b,-,pb,one,-,-,warp,-⟩ := Mma.Export.pv_block hp hX hf base gw ⟨jp,hpq⟩
  have pv : pcw ∈ [2530,2533,2535,2537,2539,2541,2543,2545] := by
    obtain rfl := hpq
    fin_cases jp <;> decide
  obtain ⟨lead,-⟩ := mma_leader hp hX hf gw
  have lead2 : Protocol.KV.leader L X (t/L.block) 7 = gq := by rw [cw]; exact lead
  have hg := Frame.lt_of_get hX gw
  rcases Nat.lt_or_ge r b with big | small
  · refine .inr (.inl ?_)
    have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 r)) kq
    change okPolls ((Object.prob (MbarRow.slot2 r)).loc L (gq/L.block)) ((X.tr gq).take kq) =
      (Object.prob (MbarRow.slot2 r)).visits (pollRound 2510 ((X.tr gq).take kq)) at cnt
    rw [pb,← cw] at cnt
    have vis : (Object.prob (MbarRow.slot2 r)).visits b = (b+2-1-r%2)/2 := rfl
    have hk : kq < (X.tr gq).length := (List.getElem?_eq_some_iff.mp gw).1
    have := ld_before_mma hp hX hf safe base rows init words hc he (.inr rfl) lt rfl s1
      (k := kq) (by rw [lead2]; exact hk) (by rw [lead2,cnt,vis]; omega)
    rw [lead2] at this
    exact this
  · refine .inl (.inl (.inl ?_))
    have lpos := Protocol.Scalar.count rows ht Object.done k0
    change okPolls (Object.done.loc L (t/L.block)) ((X.tr t).take k0) =
      Object.done.visits (pollRound 2239 ((X.tr t).take k0)) at lpos
    rw [s2] at lpos
    have vis : Object.done.visits r = (r+1-1-0)/1 := rfl
    obtain ⟨jp',pcj,pj,acq,scj,hjk,hwj,hq⟩ := UnitHandoff.exists_poll
      (m := Object.done.loc L (t/L.block)) (h := t) (f := k0) (c := b-1)
      (by rw [lpos,vis]; omega)
    have few := pv_commits_before hp hX hf rows words (c := t/L.block) hg gw pv warp pb
    have lent : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
    exact mma_done_lane hp hX hf safe rows init words hc (o := Object.done) (Or.inr rfl) lt rfl
      hwj hq gw (by rw [← lead2, cw]) (by dsimp only; omega)
      (.single (.inl (po_of_source_not_access rfl hjk lent (by rw [hwj]; rfl))))

/-- **The epilogue's load and an MMA writing one of its cells are ordered**: the MMA is done before
the load by the epilogue's poll of `o_final`. -/
public theorem ld_e_mma (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t k0 a vals sh j w}
    (he : X.get (t,k0) = some ⟨2607,.tc (.ld a vals sh)⟩)
    (hm : X.MmaCell w (tcDataCell L t sh a j)) : WriteBefore L X w (t,k0) := by
  obtain ⟨pcw,d,s,acc,mask,gw,cw,-,-,-,-,kw⟩ := mma_write_cell hp hX hf base hm
  obtain ⟨gq,kq⟩ := w
  dsimp only at cw
  obtain ⟨jw,l,q,ac,sc,hjw,hpoll⟩ := Export.epilogue_event_poll hp hX hf he (fun _ => nofun)
    (by omega) (by omega)
  have lent : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
  exact .of_done (mma_done_final hp hX hf rows init gw (by
      rcases kw with ⟨j,h,-⟩ | ⟨j,h,-⟩
      · exact .inl ⟨j,h⟩
      · exact .inr ⟨j,h⟩) hpoll cw
    (.single (.inl (po_of_source_not_access rfl hjw lent (by rw [hpoll]; rfl)))))

end PTX.Kernels.InklingRelDecode.Proof.Tmem
