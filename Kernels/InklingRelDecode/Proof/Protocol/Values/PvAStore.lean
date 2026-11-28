-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.ASource
public import Kernels.InklingRelDecode.Proof.Softmax.Export.StoreRank
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Protocol.Values.ACellForm
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.ARead
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Handoff
import Kernels.InklingRelDecode.Proof.Protocol.Values.QkStoreRound
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreMma
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Common.UbPrefix
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The source of a PV MMA's A read is a probability store

Every cell of the A operand (lane `32 q + l`, column `ba + c`) is written by the probability store
of the data thread `32 q + l` (columns `ba … ba + 31`) or `32 q + l + 16` (columns `ba + 32 …`) of
round `b - 1`: the MMA lane's polls observe lane zero's publication of a round at least `b - 1`,
the peers of lane zero's rendezvous at pc 1012 are the data threads, and every round up to the
rendezvous's has its store before it (`Softmax.Export.store_of_round`). The QK MMA that also
writes the cell is not the source: it is done before the store (`qk_store_round`), and the
source is the latest write before the read. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The data thread of a lane and a column of the probability tile. -/
theorem thread_of_cell (L : Launch) (hb : L.block = 256) (c q l col0 : Nat) (hq : q < 4)
    (hl : l < 16) (hc : col0 < 64) :
    ∃ h jj, h % L.block < 128 ∧ h / L.block = c ∧ jj < 32 ∧
      h % L.block / 32 % 4 * 32 + laneOf L h % 16 = 32 * q + l ∧
      (if laneOf L h < 16 then 0 else 32) + jj = col0 := by
  unfold laneOf
  simp only [hb]
  by_cases h32 : col0 < 32
  · exact ⟨c * 256 + 32 * q + l, col0, by omega, by omega, h32, by omega, by
      split_ifs <;> omega⟩
  · exact ⟨c * 256 + 32 * q + l + 16, col0 - 32, by omega, by omega, by omega, by omega, by
      split_ifs <;> omega⟩

/-- An event at pc 1009 without undefined behaviour is a `tcgen05.st`. -/
theorem st_kind (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {g j : Nat} {k : Kind}
    (he : X.get (g, j) = some ⟨1009, k⟩) (nu : ∀ f, k ≠ .ub f) :
    ∃ a vals sh, k = .tc (.st a vals sh) := by
  have hd := Lib.tcdata_event hX he nu
  have hd' : isTcData ⟨1009, k⟩ = true := by rw [hd]; simp [Lib.dataPcs]
  obtain ⟨kk, rfl⟩ : ∃ kk, k = .tc kk := by
    cases k <;> first | exact ⟨_, rfl⟩ | simp [isTcData] at hd'
  have tc : isTcColl ⟨1009, .tc kk⟩ = true := by
    cases kk <;> simp [isTcData, isTcColl] at hd' ⊢
  obtain ⟨i, w, -, -, -, sta⟩ := Export.st_round hp hX hf base he tc (.inl rfl)
  cases kk <;> simp [tcStatic, Lib.opStatic] at sta ⊢

/-- **A PV MMA's A read has a probability store as its source.** -/
public theorem pv_a_store (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hWrites : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) {r : EvId} {cell : Cell}
    (hr : X.MmaACell r cell) :
    ∃ src a vals sh j, ReadSource L X .a src r cell ∧
      X.get src = some ⟨1009, .tc (.st a vals sh)⟩ ∧ j < vals.length ∧
      cell = tcDataCell L src.1 sh a j ∧
      pollRound 1257 ((X.tr src.1).take src.2) = pollRound 2510 ((X.tr r.1).take r.2) ∧
      src.1 / L.block = r.1 / L.block := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨src, hsrc, -⟩ := a_read_source hp hX hf hu safe base rows init hG hWrites ht hmd hr
  obtain ⟨g, kp⟩ := r
  obtain ⟨d, s, acc, mask, index, b0, ⟨pc, he⟩, hac⟩ := id hr
  obtain ⟨hmask, lo, hi, bc, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j, -, -, none, -⟩ := qk
    simp [aCell, none] at hac
  obtain ⟨j, hpcj, hd256, -, hdesc⟩ := pv
  obtain ⟨b, -, pb, one, p2462, ⟨j', hat⟩, warp, -⟩ :=
    Mma.Export.pv_block hp hX hf base he ⟨j, hpcj⟩
  have hj8 := j'.isLt
  obtain ⟨hcta, hlo, hhi⟩ := mma_a_range hp hX hf base he hat hr
  simp only at hcta
  obtain ⟨c1, c2, c3, c4⟩ := a_cell_form hdesc hat (by omega) (lo.trans hi.symm) hac
  have hg := Frame.lt_of_get hX he
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 hg
  have lent : kp < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have cz : g / L.block * L.block / L.block = g / L.block := by simp [hp.block]
  have lp : g / L.block * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
  obtain ⟨lead, -⟩ := mma_leader hp hX hf he
  simp only at lead
  have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 (b - 1))) kp
  change okPolls ((Object.prob (MbarRow.slot2 (b - 1))).loc L (g / L.block)) ((X.tr g).take kp) =
    (Object.prob (MbarRow.slot2 (b - 1))).visits (pollRound 2510 ((X.tr g).take kp)) at cnt
  rw [pb] at cnt
  have vis : (Object.prob (MbarRow.slot2 (b - 1))).visits b = (b + 2 - 1 - (b - 1) % 2) / 2 := rfl
  have hk : kp < (X.tr (Protocol.KV.leader L X (g / L.block) 7)).length := by
    rw [lead]; exact lent
  have polls : (b - 1) / 2 + 1 ≤ okPolls ((Object.prob (MbarRow.slot2 (b - 1))).loc L
      (g / L.block)) ((X.tr (Protocol.KV.leader L X (g / L.block) 7)).take kp) := by
    rw [lead, cnt, vis]; omega
  obtain ⟨ia, l, tx, n, rel, sc, arr, hn, -⟩ := arrival_to_mma hp hX hf rows init words hc hk polls
  obtain ⟨u, cb, hu1, bar⟩ := Softmax.Export.arrive_source hp hX arr
  obtain ⟨-, pn⟩ := Softmax.Export.arrival_polls hp hX hf arr
  subst hu1
  rw [poll_keeps 1257 bar] at pn
  have passed : u + 1 < (X.tr (g / L.block * L.block)).length :=
    (List.getElem?_eq_some_iff.mp arr).1
  obtain ⟨hh, jj, h1, h2, h3, h4, h5⟩ := thread_of_cell L hp.block (g / L.block) (index / 32 / 16)
    (index / 32 % 16) (8 * j'.val + index % 32 / 4) (by omega) (by omega) (by omega)
  obtain ⟨ih, cb', hbar, -, p1, -⟩ := peer_bar hp hX hf safe (t := g / L.block * L.block)
    (h := hh) (Or.inr (Or.inr (Or.inr rfl))) bar passed lp h1 (by rw [h2, cz])
  rw [pn] at p1
  obtain ⟨k, kd, hkb, hy0, hclean, hrd⟩ := Softmax.Export.store_of_round hp hX hf hbar
    (noUbUpto hX hbar (fun _ => nofun) (Nat.le_succ _)) p1 (r := b - 1) (by omega)
  obtain ⟨sa, svals, ssh, rfl⟩ := st_kind hp hX hf base hy0 hclean
  have hy := hy0
  have tcst : isTcColl ⟨1009, .tc (.st sa svals ssh)⟩ = true := rfl
  obtain ⟨i1, w1, s1, -, -, sta⟩ := Export.st_round hp hX hf base hy tcst (.inl rfl)
  have haddr := pst_address sta
  have i1eq : i1 = b - 1 := by omega
  subst i1eq
  obtain ⟨i2, k2, -, hs2⟩ := st_static hp hX hf base hy
  rcases hs2 with ⟨h0, -⟩ | ⟨-, -, hsh, hlen⟩
  · omega
  subst hsh
  have hcst : cell = tcDataCell L hh (.s16x32bx2 32) sa jj := by
    have hsp := cell_split L hh (sa % 2 ^ 21) 32 (sa / 2 ^ 21) jj (by omega)
    rw [show sa % 2 ^ 21 + sa / 2 ^ 21 * 2 ^ 21 = sa by omega] at hsp
    rw [hsp]
    have hceq : cell = ⟨cell.cta, cell.lane, cell.column⟩ := rfl
    rw [hceq]
    simp only [Cell.mk.injEq]
    refine ⟨by omega, by omega, by omega⟩
  have hwst : TmemWrite L X (hh, k) cell :=
    .inr (.inl ⟨sa, svals, .s16x32bx2 32, jj, ⟨1009, hy⟩, by omega, hcst⟩)
  have sdb := store_before_mma hp hX hf safe base rows init words hc hy (.inl rfl) h1 h2 hrd hk
    polls
  rw [lead] at sdb
  have cyc : ∀ {x y : EvId}, Relation.TransGen (TcStep L X) x y →
      Relation.TransGen (TcStep L X) y x → False := fun h1 h2 =>
    tcStep_acyclic hX hG _ (h1.trans h2)
  obtain ⟨hne, hw, hwb, h4', hlive⟩ := readSource_a.mp hsrc
  have hnotmma : ∀ {e : EvId} {pc' d' s' a' m'}, X.get e = some ⟨pc', .tc (.mma d' s' a' m')⟩ →
      e ≠ (hh, k) := by
    intro e pc' d' s' a' m' h heq
    rw [heq, hy] at h
    simp at h
  rcases tmemWrite_of_no_copy (Lib.no_cp hX) (no_shift hX) hw with hm | hs
  · exfalso
    obtain ⟨pcw, dw, sw, aw, mw, gw, cw, l1, h1', -, -, kw⟩ := mma_write_cell hp hX hf base hm
    rcases kw with ⟨jq, hpq, hdq, -⟩ | ⟨-, -, hd, -⟩
    swap
    · omega
    obtain ⟨b2, hd2, q1, -⟩ := Mma.Export.qk_block hp hX hf base gw ⟨jq, hpq⟩
    obtain ⟨gq, ks⟩ := src
    simp only at cw
    have cta : gq / L.block = g / L.block := by rw [← cw, hcta]
    have thr : g = gq := mma_thread hp hX hf he gw cta.symm
    subst thr
    have hlt : ks < kp :=
      tcStep_same_thread (tcStep_acyclic hX hG) hwb.tcStep rfl (by rw [he]; rfl)
    have mono := countP_take_mono (okPollAt 2462) (X.tr g) hlt.le
    change pollRound 2462 _ ≤ pollRound 2462 _ at mono
    have par : b2 % 2 = (b - 1) % 2 := by omega
    obtain ⟨b3, r3, pb3, s3, -, o⟩ := qk_store_round hp hX hf safe base rows init gw ⟨jq, hpq⟩ hy
      (show g / L.block = hh / L.block by rw [h2]) (by omega)
    simp only at pb3 s3 q1
    have hb3 : b3 = b2 := by omega
    have hr3 : r3 = b - 1 := by omega
    subst hb3 hr3
    rcases o with ⟨-, dn⟩ | ⟨lt3, -⟩
    swap
    · omega
    rcases h4' (hh, k) hwst with h | h | h | h | h | h
    · exact hnotmma gw h.symm
    · exact cyc dn.tcStep h.tcStep
    · exact hnotmma he h.symm
    · exact cyc h.tcStep sdb.tcStep
    · exact cyc h.tcBefore.tcStep sdb.tcStep
    · exact cyc h.tcBefore.tcStep sdb.tcStep
  · obtain ⟨lts, -, h1s | h2s⟩ := st_write_cell hp hX hf base hs
    · obtain ⟨a', vals', ba, w, j2, gs, rfl, hba, hj2, hc2⟩ := h1s
      obtain ⟨i3, k3, -, hs3⟩ := st_static hp hX hf base gs
      rcases hs3 with ⟨h0, -⟩ | ⟨-, -, -, hlen2⟩
      · omega
      obtain ⟨c1', c2', c3'⟩ := p_cols (L := L) (g := src.1) (w := w) hba hj2
      rw [← hc2] at c1' c2' c3'
      have cta2 : src.1 / L.block = g / L.block := by rw [← c3', hcta]
      have tcs : isTcColl ⟨1009, .tc (.st (ba + w * 2 ^ 21) vals' (.s16x32bx2 32))⟩ = true :=
        rfl
      obtain ⟨rs, wst2, s1s, -, s3s, sta2⟩ := Export.st_round hp hX hf base gs tcs (.inl rfl)
      have haddr2 := pst_address sta2
      refine ⟨src, _, vals', _, j2, hsrc, gs, by omega, hc2, ?_, cta2⟩
      have rlt : rs < b := by
        by_contra hge
        have few := pv_scores_before hp hX hf rows words (c := g / L.block)
          (s := MbarRow.slot2 rs) hg warp p2462 (by show rs % 2 = (b - 1) % 2; omega)
        simp only [ite_true] at s3s
        have dn := mma_before_pst hp hX hf safe rows init words he gs lts cta2.symm s1s s3s
          (by omega)
        exact cyc dn.tcStep hwb.tcStep
      have rge : b - 1 ≤ rs := by
        rcases h4' (hh, k) hwst with h | h | h | h | h | h
        · subst h
          simp only at s1s
          omega
        · have hthr : (hh, k).1 = src.1 :=
            (ss_one hp hX hf base (x := (hh, k)) (y := src) (cell := cell)
              ⟨_, _, _, jj, ⟨1009, hy⟩, by omega, hcst⟩
              ⟨_, _, _, j2, ⟨1009, gs⟩, by omega, hc2⟩).2
          have lt := tcStep_same_thread (tcStep_acyclic hX hG) h.tcStep hthr
            (by rw [gs]; rfl)
          have mono := countP_take_mono (okPollAt 1257) (X.tr hh) lt.le
          change pollRound 1257 _ ≤ pollRound 1257 (List.take src.2 (X.tr hh)) at mono
          have e1 : src.1 = hh := hthr.symm
          rw [e1] at s1s
          simp only at mono
          omega
        · exact absurd (h ▸ hy) (by rw [he]; simp)
        · exact (cyc h.tcStep sdb.tcStep).elim
        · exact (cyc h.tcBefore.tcStep sdb.tcStep).elim
        · exact (cyc h.tcBefore.tcStep sdb.tcStep).elim
      show pollRound 1257 _ = pollRound 2510 ((X.tr g).take kp)
      omega
    · obtain ⟨a', vals', w, j2, gs, rfl, hj2, hc2⟩ := h2s
      obtain ⟨c1', c2', c3'⟩ := o_cols (L := L) (g := src.1) (w := w) hj2
      rw [← hc2] at c1'
      omega

end PTX.Kernels.InklingRelDecode.Proof.Tmem
