-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreMma
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BlockCounts
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Handoff
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Kernel.Frame
import Lemmas.Kernel.Safety.TableU
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # A score load is ordered with every writer of its cells

The load of round `r` (pc 1265) reads the 128 columns of the score buffer of parity `r % 2`, 64
registers per lane. Its writers are the QK MMAs of that buffer and the probability stores of the
buffer by the lanes of its warp. A QK MMA of a block at most `r` is done before the load by the
load's own poll of the score slot; a later one follows the load's wait through lane zero's
publication. A store of an earlier round is before the load, and a store of the round or a later
one after it, by the mandatory rendezvous between them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The cell of a score load's register**: of its round's score buffer. -/
public theorem ld_s_cell (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t k0 a vals sh j}
    (he : X.get (t,k0) = some ⟨1265,.tc (.ld a vals sh)⟩) (hj : j < vals.length) :
    ∃ r, j < 64 ∧ t%L.block < 128 ∧ pollRound 1257 ((X.tr t).take k0) = r+1 ∧
      Softmax.Export.mandatory ((X.tr t).take k0) + 2 = 4*r + (if r = 0 then 2 else 0) ∧
      tcDataCell L t sh a j = ⟨t/L.block, t%L.block/32%4*32 + laneOf L t % 16,
        r%2*128 + (if laneOf L t < 16 then 0 else 64) + j⟩ := by
  have lt := Export.tc_data_lane hp hX hf he (by rfl)
  have tc : isTcColl ⟨1265,.tc (.ld a vals sh)⟩ = true := rfl
  obtain ⟨r,wd,s1,-,s3,sta,-⟩ := Export.ld_round hp hX hf base he tc (.inl rfl)
  obtain ⟨i,kk,hk4,-,hsh,hlen⟩ := ld_static hp hX hf base he
  simp only [tcStatic,Lib.opStatic,Lib.bcastOffset] at sta
  simp at sta
  obtain ⟨rfl,-⟩ := sta
  obtain rfl := hsh
  refine ⟨r,by omega,lt,s1,by simpa using s3,?_⟩
  exact cell_split L t (r%2*128) 64 ((Lib.word wd).toNat%4) j (by omega)

/-- **The load of round `r` follows its poll of the score slot with `r / 2` earlier polls.** -/
public theorem ld_s_poll (rows : MbarRows Q L X) {t k0 r}
    (ht : t < L.threads) (s1 : pollRound 1257 ((X.tr t).take k0) = r+1) :
    ∃ jp pcj pj acq scj, jp < k0 ∧
      X.get (t,jp) = some ⟨pcj,.wait ((Object.score (MbarRow.slot2 r)).loc L (t/L.block)) pj true
        acq scj⟩ ∧
      okPolls ((Object.score (MbarRow.slot2 r)).loc L (t/L.block)) ((X.tr t).take jp) = r/2 := by
  have lpos := Protocol.Scalar.count rows ht (Object.score (MbarRow.slot2 r)) k0
  change okPolls ((Object.score (MbarRow.slot2 r)).loc L (t/L.block)) ((X.tr t).take k0) =
    (Object.score (MbarRow.slot2 r)).visits (pollRound 1257 ((X.tr t).take k0)) at lpos
  rw [s1] at lpos
  have vis : (Object.score (MbarRow.slot2 r)).visits (r+1) = (r+1+2-1-r%2)/2 := rfl
  exact UnitHandoff.exists_poll (m := (Object.score (MbarRow.slot2 r)).loc L (t/L.block))
    (h := t) (f := k0) (c := r/2) (by rw [lpos,vis]; omega)

/-- **A QK MMA with at most `r / 2` earlier commits to the score slot is done before the score load
of round `r`**: by the load's own poll of the slot with `r / 2` earlier polls. -/
public theorem ld_qk_done (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (rows : MbarRows Q L X)
    (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh r gq kq pcw d s acc mask}
    (he : X.get (t,k0) = some ⟨1265,.tc (.ld a vals sh)⟩) (lt : t%L.block < 128)
    (s1 : pollRound 1257 ((X.tr t).take k0) = r+1)
    (gw : X.get (gq,kq) = some ⟨pcw,.tc (.mma d s acc mask)⟩)
    (cw : t/L.block = gq/L.block)
    (few : ((X.tr gq).take kq).countP
      (commitsTo ((Object.score (MbarRow.slot2 r)).loc L (t/L.block))) ≤ r/2) :
    DoneBefore L X (gq,kq) (t,k0) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  obtain ⟨lead,-⟩ := mma_leader hp hX hf gw
  have lead2 : Protocol.KV.leader L X (t/L.block) 7 = gq := by rw [cw]; exact lead
  obtain ⟨jp,pcj,pj,acq,scj,hjk,hwj,hq⟩ := ld_s_poll rows ht s1
  have lent : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
  exact mma_done_lane hp hX hf safe rows init words hc (o := Object.score (MbarRow.slot2 r))
    (Or.inl ⟨_,rfl⟩) lt rfl hwj hq gw (by rw [← lead2, cw]) few
    (.single (.inl (po_of_source_not_access rfl hjk lent (by rw [hwj]; rfl))))

/-- **A probability store of a cell of a score load** is of a round of its buffer's parity: of an
earlier round and before the load, or of a later one and after it. -/
public theorem ld_s_pst (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {t k0 a vals sh j w}
    (he : X.get (t,k0) = some ⟨1265,.tc (.ld a vals sh)⟩) (hj : j < vals.length)
    (hs : StoreCell L X w (tcDataCell L t sh a j)) :
    ∃ r r', pollRound 1257 ((X.tr t).take k0) = r+1 ∧ pollRound 1257 ((X.tr w.1).take w.2) = r'+1 ∧
      r'%2 = r%2 ∧
        ((r' < r ∧ WriteBefore L X w (t,k0)) ∨ (r ≤ r' ∧ ReadBefore L X .ld (t,k0) w)) := by
  have ht := Frame.lt_of_get hX he
  obtain ⟨r,hj64,lt,s1,s3,cellEq⟩ := ld_s_cell hp hX hf base he hj
  rw [cellEq] at hs
  have nuk := Frame.noUbBefore_of_get hX he
  obtain ⟨gq,kq⟩ := w
  obtain ⟨lt',tt',kw⟩ := st_write_cell hp hX hf base hs
  dsimp only at lt' tt'
  rcases kw with ⟨a',vals',ba,wd',jj,hy,ha',hb,hj',hc'⟩ | ⟨a',vals',wd',jj,hy,ha',hj',hc'⟩
  swap
  · exfalso
    obtain ⟨c1,-,-⟩ := o_cols (L := L) (g := gq) (w := wd') hj'
    rw [ha'] at hc'
    rw [← hc'] at c1
    dsimp only at c1
    split_ifs at c1 <;> omega
  rw [ha',cell_split L gq ba 32 wd' jj (by omega)] at hc'
  simp only [TcMma.Cell.mk.injEq] at hc'
  obtain ⟨hcta,hrow,hcol⟩ := hc'
  unfold laneOf at hrow hcol
  have tcs : isTcColl ⟨1009,.tc (.st a' vals' (.s16x32bx2 32))⟩ = true := rfl
  obtain ⟨r',w'',s1',-,s3',sta'⟩ := Export.st_round hp hX hf base hy tcs (.inl rfl)
  have haddr := pst_address sta'
  have warp : t%L.block/32 = gq%L.block/32 := by omega
  have sw : SameWarp L gq t := ⟨⟨Frame.lt_of_get hX hy,ht,by omega⟩,warp.symm⟩
  have swt : SameWarp L t gq := ⟨⟨ht,Frame.lt_of_get hX hy,by omega⟩,warp⟩
  have hbr : ba = r'%2*128 := by omega
  have par : r'%2 = r%2 := by split_ifs at hcol <;> omega
  have lenk : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
  have lenq : kq < (X.tr gq).length := (List.getElem?_eq_some_iff.mp hy).1
  rcases Nat.lt_or_ge r' r with early | late
  · refine ⟨r,r',s1,s1',par,.inl ⟨early,.inr (.inl ⟨⟨_,_,_,1009,hy⟩,.inr (.inl ⟨sw,.inl ?_,
      ⟨_,_,_,1009,hy⟩,⟨_,_,_,1265,he⟩⟩)⟩)⟩⟩
    refine (mandatory_handoff hp hX hf safe hy lt' lt (by omega) lenk
      (fun u ev hu' get => nuk u hu' ev get) ?_).2.1
    simp at s3'
    by_cases h0 : r = 0 <;> simp [h0] at s3 <;> omega
  · refine ⟨r,r',s1,s1',par,.inr ⟨late,.inr ⟨swt,.inl ?_,⟨_,_,_,1265,he⟩,⟨_,_,_,1009,hy⟩⟩⟩⟩
    refine (mandatory_handoff hp hX hf safe he lt lt' (by omega) lenq
      (fun u ev hu' get => Frame.noUbBefore_of_get hX hy u hu' ev get) ?_).2.1
    simp at s3'
    by_cases h0 : r = 0 <;> simp [h0] at s3 <;> omega


/-- **A QK MMA of a later pair of blocks follows the score load**: the MMA waits for the softmax's
release of the buffer, which follows the load's wait. -/
public theorem ld_s_late (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh r gq kq pcw d s acc
      mask b}
    (he : X.get (t,k0) = some ⟨1265,.tc (.ld a vals sh)⟩) (lt : t%L.block < 128)
    (s1 : pollRound 1257 ((X.tr t).take k0) = r+1)
    (gw : X.get (gq,kq) = some ⟨pcw,.tc (.mma d s acc mask)⟩) (cw : t/L.block = gq/L.block)
    (q2 : pollRound 2510 ((X.tr gq).take kq) = b-1) (par : b%2 = r%2) (big : r/2 < b/2) :
    WaitBefore L X .waitLd (t,k0) (gq,kq) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  obtain ⟨lead,-⟩ := mma_leader hp hX hf gw
  have lead2 : Protocol.KV.leader L X (t/L.block) 7 = gq := by rw [cw]; exact lead
  have hg := Frame.lt_of_get hX gw
  have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 r)) kq
  change okPolls ((Object.prob (MbarRow.slot2 r)).loc L (gq/L.block)) ((X.tr gq).take kq) =
    (Object.prob (MbarRow.slot2 r)).visits (pollRound 2510 ((X.tr gq).take kq)) at cnt
  rw [q2,← cw] at cnt
  have vis : (Object.prob (MbarRow.slot2 r)).visits (b-1) = (b-1+2-1-r%2)/2 := rfl
  have hk : kq < (X.tr gq).length := (List.getElem?_eq_some_iff.mp gw).1
  have := ld_before_mma hp hX hf safe base rows init words hc he (.inl rfl) lt rfl s1
    (k := kq) (by rw [lead2]; exact hk) (by rw [lead2,cnt,vis]; omega)
  rw [lead2] at this
  exact this

/-- **A score load and a writer of one of its cells are ordered.** -/
public theorem ld_s_order (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh j w}
    (he : X.get (t,k0) = some ⟨1265,.tc (.ld a vals sh)⟩) (hj : j < vals.length)
    (hw : TmemWrite L X w (tcDataCell L t sh a j)) :
    WriteBefore L X w (t,k0) ∨ ReadBefore L X .ld (t,k0) w := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  obtain ⟨r,hj64,lt,s1,s3,cellEq⟩ := ld_s_cell hp hX hf base he hj
  rw [cellEq] at hw
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  have nuk := Frame.noUbBefore_of_get hX he
  rcases tmemWrite_of_no_copy (Lib.no_cp hX) (no_shift hX) hw with hm | hs
  · obtain ⟨pcw,d,s,acc,mask,gw,cw,l1,h1,-,-,kw⟩ := mma_write_cell hp hX hf base hm
    obtain ⟨gq,kq⟩ := w
    dsimp only at cw l1 h1
    rcases kw with ⟨jq,hpq,hd,-⟩ | ⟨-,-,hd,-⟩
    swap
    · exfalso
      split_ifs at l1 h1 <;> omega
    obtain ⟨b,hdb,q1,q2,warp,-⟩ := Mma.Export.qk_block hp hX hf base gw ⟨jq,hpq⟩
    have qkl : pcw ∈ [2483,2486,2488,2490,2492,2494,2496,2498] := by
      obtain rfl := hpq
      fin_cases jq <;> decide
    obtain ⟨lead,-⟩ := mma_leader hp hX hf gw
    have lead2 : Protocol.KV.leader L X (t/L.block) 7 = gq := by rw [cw]; exact lead
    have hg := Frame.lt_of_get hX gw
    have par : b%2 = r%2 := by split_ifs at l1 h1 <;> omega
    rcases Nat.lt_or_ge (r/2) (b/2) with big | small
    · exact .inr (.inl (ld_s_late hp hX hf safe base rows init he lt s1 gw cw q2 par big))
    · have few := qk_commits_before hp hX hf rows words (c := t/L.block)
        (s := MbarRow.slot2 r) hg gw qkl warp q1 (by show r%2 = b%2; omega)
      exact .inl (.inl (.inl (ld_qk_done hp hX hf safe rows init he lt s1 gw cw (by omega))))
  · obtain ⟨r1, r2, -, -, -, h⟩ := ld_s_pst hp hX hf safe base he hj (by rw [cellEq]; exact hs)
    exact Or.elim h (fun h => .inl h.2) fun h => .inr h.2

end PTX.Kernels.InklingRelDecode.Proof.Tmem
