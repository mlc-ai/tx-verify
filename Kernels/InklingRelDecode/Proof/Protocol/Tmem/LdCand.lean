-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrder
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.CellCover
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarCommits
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarLane
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.CommitCount
import Kernels.InklingRelDecode.Proof.Protocol.P.DoneBudget
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaDone
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Common.Export.EpiPoll
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Kernel.Frame

@[expose] public section

/-! # A load has a writer before it

The score load of round `r` follows its poll of the score slot with `r / 2` earlier polls, which
observes the score commit of block `r`; the QK steps of the block precede the commit in the MMA lane
and write every cell of the load, and they are done before it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A score load has a QK MMA before it that writes the cell**: of a block `b` of the load's
round's parity (any step `js`) with `r / 2 ≤ b / 2`. -/
public theorem ld_s_cand (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh j}
    (he : X.get (t,k0) = some ⟨1265,.tc (.ld a vals sh)⟩) (hj : j < vals.length)
    (js : Fin 8) :
    ∃ w, TmemWrite L X w (tcDataCell L t sh a j) ∧ WriteBefore L X w (t,k0) ∧
      ∃ r b, pollRound 1257 ((X.tr t).take k0) = r+1 ∧ r/2 ≤ b/2 ∧ b%2 = r%2 ∧
        ∃ dst s acc mask, X.get w = some ⟨Lib.qkIssue js,.tc (.mma dst s acc mask)⟩ ∧
          pollRound 2462 ((X.tr w.1).take w.2) = b+1 := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  obtain ⟨r,hj64,lt,s1,-,cellEq⟩ := ld_s_cell hp hX hf base he hj
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  obtain ⟨jp,pcj,pj,acq,scj,hjk,hwj,hq⟩ := ld_s_poll rows ht s1
  obtain ⟨hy,cy,wy⟩ := Protocol.KV.leader_warp (X := X) hp hc (by decide : 7<8)
  have O := notification hp hX hf rows init (c := t/L.block) (.inl ⟨MbarRow.slot2 r,rfl⟩)
  obtain ⟨ic,pc',sp,rank,hget,hm,-,hcnt,-,-⟩ := O.observes hX
    (lane_reach hp hX hf safe rows init words hc lt rfl (.inl ⟨MbarRow.slot2 r,rfl⟩)) hwj hq
  obtain ⟨sp',get2,slot⟩ := score_receipt (c := t/L.block) (s := MbarRow.slot2 r) hp hX hf rows
    hy hget (by simp [commitsTo,hm])
  obtain ⟨kR,ltk,d',s',a',m',gw,q⟩ := Mma.Export.score_history hp hX hf words hu get2 js
  obtain ⟨b,hdb,q1,-,warp,-⟩ := Mma.Export.qk_block hp hX hf base gw ⟨js,rfl⟩
  obtain ⟨hmask,lo,hi,bc,qk|pv⟩ := Mma.Export.columns hp hX hf base gw
  swap
  · obtain ⟨j2,hpc2,-⟩ := pv
    have ne : ∀ j j' : Fin 8, Lib.qkIssue j ≠ Lib.pvIssue j' := by decide
    exact (ne js j2 hpc2).elim
  obtain ⟨j0,-,-,-,desc⟩ := qk
  have par : (MbarRow.slot2 r).val = r%2 := rfl
  have hpar : r%2 = b%2 := by
    rw [← par,slot]
    omega
  have cnt : r/2 ≤ b/2 := by
    have := Protocol.Scalar.commits_before_commit hp hX hf rows words (c := t/L.block)
      (s := MbarRow.slot2 r) hy wy get2 (b := b) (q.symm.trans q1) (by omega)
    exact (le_of_eq hcnt.symm).trans this
  refine ⟨(Protocol.KV.leader L X (t/L.block) 7,kR),.inl ?_,.of_done ?_,r,b,s1,cnt,hpar.symm,
    _,_,_,_,gw,q1⟩
  · have := mma_writes_cell (s := s') (d := d') (q := t%L.block/32%4) (l := laneOf L t % 16)
      (col := r%2*128 + (if laneOf L t < 16 then 0 else 64) + j) (cta := t/L.block)
      (by rw [desc]; exact Lib.qkDesc_valid) (by rw [desc]; rfl) (by rw [desc]; rfl)
      (by rw [desc]; rfl) (by rw [desc]; rfl) (by rw [lo,cy]) (by rw [hi,lo]) (by omega)
      (by omega) (by unfold laneOf; omega)
      (by split_ifs <;> omega) (by split_ifs <;> omega)
    obtain ⟨row,col,hw⟩ := this
    subst hmask
    rw [cellEq]
    exact ⟨d',s',a',[0,0,0,0],row,col,⟨_,gw⟩,hw⟩
  · have mono := countP_take_mono (commitsTo ((Object.score (MbarRow.slot2 r)).loc L (t/L.block)))
      (X.tr (Protocol.KV.leader L X (t/L.block) 7)) ltk.le
    exact ld_qk_done hp hX hf safe rows init he lt s1 gw cy.symm (mono.trans hcnt.le)

/-- **A PV issue of the CTA's MMA lane writes every cell of an accumulator load.** -/
theorem pv_cell_write (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t j g kR d' s' a' m'}
    (gw : X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma d' s' a' m')⟩) (cy : g/L.block = t/L.block)
    (hj : j < 64) :
    X.MmaCell (g,kR) ⟨t/L.block, t%L.block/32%4*32 + laneOf L t % 16,
      256 + (if laneOf L t < 16 then 0 else 64) + j⟩ := by
  obtain ⟨hmask,lo,hi,bc,qk|pv⟩ := Mma.Export.columns hp hX hf base gw
  · obtain ⟨j2,hpc2,-⟩ := qk
    have ne : ∀ j : Fin 8, Lib.pvIssue 7 ≠ Lib.qkIssue j := by decide
    exact (ne j2 hpc2).elim
  obtain ⟨j0,hpc0,hd0,-,desc⟩ := pv
  have := mma_writes_cell (s := s') (d := d') (q := t%L.block/32%4) (l := laneOf L t % 16)
    (col := 256 + (if laneOf L t < 16 then 0 else 64) + j) (cta := t/L.block)
    (by rw [desc]; exact Lib.pvDesc_valid) (by rw [desc]; rfl) (by rw [desc]; rfl)
    (by rw [desc]; rfl) (by rw [desc]; rfl) (by rw [lo,cy]) (by rw [hi,lo]) (by omega)
    (by omega) (by unfold laneOf; omega) (by split_ifs <;> omega) (by split_ifs <;> omega)
  obtain ⟨row,col,hw⟩ := this
  subst hmask
  exact ⟨d',s',a',[0,0,0,0],row,col,⟨_,gw⟩,hw⟩

/-- **An accumulator load of round `r` has a PV MMA before it that writes the cell**: the last step
of block `r - 1`, done before the load by its poll of the done slot with `r - 1` earlier polls. -/
public theorem ld_o_cand (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh j}
    (he : X.get (t,k0) = some ⟨2260,.tc (.ld a vals sh)⟩) (hj : j < vals.length) :
    ∃ w, TmemWrite L X w (tcDataCell L t sh a j) ∧ WriteBefore L X w (t,k0) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  have tc : isTcColl ⟨2260,.tc (.ld a vals sh)⟩ = true := rfl
  obtain ⟨r,wd,s1,s2,-,-,pos⟩ := Export.ld_round hp hX hf base he tc (.inr rfl)
  obtain ⟨kk,hk4,rfl,rfl,hj64,lt,cellEq⟩ := ld_o_cell hp hX hf base he (.inl rfl) hj
  have pos' := pos rfl
  simp at s2
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  have lpos := Protocol.Scalar.count rows ht Object.done k0
  change okPolls (Object.done.loc L (t/L.block)) ((X.tr t).take k0) =
    Object.done.visits (pollRound 2239 ((X.tr t).take k0)) at lpos
  rw [s2] at lpos
  have vis : Object.done.visits r = (r+1-1-0)/1 := rfl
  obtain ⟨jp,pcj,pj,acq,scj,hjk,hwj,hq⟩ := UnitHandoff.exists_poll
    (m := Object.done.loc L (t/L.block)) (h := t) (f := k0) (c := r-1) (by rw [lpos,vis]; omega)
  obtain ⟨hy,cy,wy⟩ := Protocol.KV.leader_warp (X := X) hp hc (by decide : 7<8)
  have O := notification hp hX hf rows init (c := t/L.block) (.inr rfl)
  obtain ⟨ic,pc',sp,rank,hget,hm,-,hcnt,-,-⟩ := O.observes hX
    (lane_reach hp hX hf safe rows init words hc lt rfl (.inr rfl)) hwj hq
  obtain ⟨sp',get2⟩ := Protocol.P.done_receipt (c := t/L.block) hp hX hf rows hy hget
    (by simp [commitsTo,hm])
  obtain ⟨kR,ltk,d',s',a',m',gw,q⟩ := Mma.Export.done_history hp hX hf words hu get2
  refine ⟨(Protocol.KV.leader L X (t/L.block) 7,kR),.inl ?_,.of_done ?_⟩
  · rw [cellEq]
    exact pv_cell_write hp hX hf base gw cy hj64
  · have mono := countP_take_mono (commitsTo (Object.done.loc L (t/L.block)))
      (X.tr (Protocol.KV.leader L X (t/L.block) 7)) ltk.le
    have lent : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
    exact mma_done_lane hp hX hf safe rows init words hc (o := Object.done) (Or.inr rfl) lt rfl
      hwj hq gw rfl (mono.trans hcnt.le)
      (.single (.inl (po_of_source_not_access rfl hjk lent (by rw [hwj]; rfl))))

/-- **The epilogue's load has the last PV step of the last block before it**, done before the load
by the epilogue's poll of `o_final`. -/
public theorem ld_e_pv7 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh}
    (he : X.get (t,k0) = some ⟨2607,.tc (.ld a vals sh)⟩) :
    ∃ g kR, g/L.block = t/L.block ∧
      (∃ d s a m, X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma d s a m)⟩) ∧
      pollRound 2510 ((X.tr g).take kR) = Lib.blocksOf Q L (t/L.block) ∧
      WriteBefore L X (g,kR) (t,k0) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  have tc : isTcColl ⟨2607,.tc (.ld a vals sh)⟩ = true := rfl
  obtain ⟨-,-,-,-,-,-,-,-,-,-,nz,-,-⟩ := Export.tc_counts hp hX hf he tc
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  obtain ⟨hy,cy,wy⟩ := Protocol.KV.leader_warp (X := X) hp hc (by decide : 7<8)
  obtain ⟨jw,l,q,ac,sc,hjw,hpoll⟩ := Export.epilogue_event_poll hp hX hf he (fun _ => nofun)
    (by omega) (by omega)
  obtain ⟨ic,spi,rank,hgc,-,-,-⟩ := poll_observes hp hX hf rows init hpoll
  have nz' : Lib.blocksOf Q L (Protocol.KV.leader L X (t/L.block) 7/L.block) ≠ 0 := by
    rw [cy]; exact nz (.inl rfl)
  obtain ⟨kR,ltk,d',s',a',m',gw,ordk⟩ := Mma.Export.final_history_ord hp hX hf words hu hgc nz'
  have lent : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨Protocol.KV.leader L X (t/L.block) 7,kR,cy,⟨d',s',a',m',gw⟩,by rw [ordk,cy],
    .of_done ?_⟩
  exact mma_done_final hp hX hf rows init gw (.inr ⟨7,rfl⟩) hpoll cy.symm
    (.single (.inl (po_of_source_not_access rfl hjw lent (by rw [hpoll]; rfl))))

/-- **The epilogue's load has a PV MMA before it that writes the cell**: the last step of the
CTA's last block, done before the load by the epilogue's poll of `o_final`. -/
public theorem ld_e_cand (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh j}
    (he : X.get (t,k0) = some ⟨2607,.tc (.ld a vals sh)⟩) (hj : j < vals.length) :
    ∃ w, TmemWrite L X w (tcDataCell L t sh a j) ∧ WriteBefore L X w (t,k0) := by
  obtain ⟨kk,hk4,rfl,rfl,hj64,lt,cellEq⟩ := ld_o_cell hp hX hf base he (.inr rfl) hj
  obtain ⟨g,kR,cy,⟨d',s',a',m',gw⟩,-,hb⟩ := ld_e_pv7 hp hX hf hu rows init he
  refine ⟨(g,kR),.inl ?_,hb⟩
  rw [cellEq]
  exact pv_cell_write hp hX hf base gw cy hj64

end PTX.Kernels.InklingRelDecode.Proof.Tmem
