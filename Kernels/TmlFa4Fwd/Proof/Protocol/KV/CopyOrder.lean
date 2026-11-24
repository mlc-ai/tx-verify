-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Order
import Kernels.TmlFa4Fwd.Proof.Lib.SmemCover
import Kernels.TmlFa4Fwd.Proof.Loader.Export.KvSlot
import Kernels.TmlFa4Fwd.Proof.Mma.Export.RelBlock
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Lemmas.Async.AsyncChain
import Lemmas.Flow.NthEv
import Lemmas.Protocol.PairTmaRing.Order
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The K/V ring: the row copies of one location are ordered

A copy of packet `t` is before a copy of a later packet of the slot: the later copy follows the
lane's poll of the empty barrier with `t / 3 + 1` earlier ones, which observes the commit with
`t / 3` earlier ones, so the eight MMAs of use `t` before it, whose operands fill the slot; the one
that reads the byte links the two copies (`kv_copy_copy`). Two copies of one packet write different
bytes (`kv_row_row`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy PTX.MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- A byte of slot `s` of the K/V ring of lane `g`'s CTA. -/
def InSlot (L : Launch) (g s : Nat) (l : Loc) : Prop :=
  ∃ off < 32768, l = ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * s + off⟩

theorem mma_covers {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue (g, k) d sp acc mask) {isB : Bool} {idx : Nat} {l : Loc}
    (hl : sp.byteLoc (if isB then .b else .a) idx = some l) :
    AsyncCovers X (g, k) (.mmaRead isB idx) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, .inl ⟨d, sp, acc, mask, hi, hl⟩⟩,
    ⟨rfl, rfl, le_rfl, by simp⟩⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The MMAs before a release read every byte of the released slot.** -/
theorem kv_release_read {i pc : Nat} {spc : TcCommit.Spec} {s : Fin 3}
    (hw : Prologue.warpIndex L g = 12) (he : X.get (g, i) = some ⟨pc, .tc (.commit spc)⟩)
    (hb : spc.mbar = obj L g (56 + 8 * s.val)) {l : Loc} (hl : InSlot L g s.val l) :
    ∃ t k' idx d sp acc mask, t % 3 = s.val ∧
      ((X.tr g).take i).countP (commitsTo (obj L g (56 + 8 * s.val))) = t / 3 ∧ k' < i ∧
      KvRead L X g k' t ∧ X.MmaIssue (g, k') d sp acc mask ∧ idx < 4096 ∧
      sp.byteLoc .b idx = some l := by
  obtain ⟨h1, h2, h3⟩ := Mma.kv_block hp hX hFw hw he (o := s) hb
  obtain ⟨off, ho, rfl⟩ := hl
  have hsh := hp.shared.1
  have hs := s.isLt
  set t := Tm.kvRels L X g i with ht
  rcases Nat.even_or_odd' t with ⟨u0, hev | hod⟩
  · -- a K slot
    have hbase : (L.sharedBase + 68608 + 32768 * s.val + 16384 * (off / 16384)) % 128 = 0 := by
      omega
    obtain ⟨j4, hj4, idx, hidx, hcov⟩ := Tm.qk_cover (off := off % 16384) hbase
      (Nat.mod_lt _ (by decide))
    obtain ⟨k', hk', u, ⟨hq, hu⟩ | ⟨-, hu⟩⟩ := h3 ⟨4 * (off / 16384) + j4, by omega⟩
    swap
    · omega
    obtain ⟨pcq, da, db, hi⟩ := hq.issue
    have hmma : X.MmaIssue (g, k') _ _ _ _ := ⟨pcq, hi⟩
    obtain ⟨-, -, -, hsp⟩ := hq.spec_eq hmma
    refine ⟨t, k', idx, _, _, _, _, h1, h2, hk', ⟨1, u, _, .inl ⟨hq, hu⟩⟩, hmma, hidx, ?_⟩
    rw [hsp]
    have hc := (hcov ⟨Tm.qkDsc, Tm.qkA L 1 ⟨4 * (off / 16384) + j4, by omega⟩,
      Tm.qkB L (2 * u % 3) ⟨4 * (off / 16384) + j4, by omega⟩, g / L.block, g / L.block, none, {}⟩
      (g / L.block) rfl rfl rfl).2 (by
        simp only [Tm.qkB]
        congr 1
        have e1 : (4 * (off / 16384) + j4) / 4 = off / 16384 := by omega
        have e2 : (4 * (off / 16384) + j4) % 4 = j4 := by omega
        rw [e1, e2]
        have : 2 * u % 3 = s.val := by rw [← hu]; exact h1
        rw [this])
    rw [hc]
    congr 2
    omega
  · -- a V slot
    have hbase : (L.sharedBase + 68608 + 32768 * s.val) % 128 = 0 := by omega
    obtain ⟨j8, hj8, idx, hidx, hcov⟩ := Tm.pv_cover hbase ho
    obtain ⟨k', hk', u, ⟨-, hu⟩ | ⟨hq, hu⟩⟩ := h3 ⟨j8, hj8⟩
    · omega
    obtain ⟨pcq, db, hi⟩ := hq.issue
    have hmma : X.MmaIssue (g, k') _ _ _ _ := ⟨pcq, hi⟩
    obtain ⟨-, -, -, hsp⟩ := hq.spec_eq hmma
    refine ⟨t, k', idx, _, _, _, _, h1, h2, hk', ⟨1, u, _, .inr ⟨hq, hu⟩⟩, hmma, hidx, ?_⟩
    rw [hsp]
    refine hcov _ _ rfl rfl ?_
    simp only [Tm.pvB]
    have : (2 * u + 1) % 3 = s.val := by rw [← hu]; exact h1
    rw [this]

omit hp hX hFw in
/-- **A row copy's bytes are its slot's.** -/
theorem copy_slot {y jc : Nat} {sp : AsyncCopy.Spec} (hC : LdCp L X y jc sp) {l : Loc}
    (hc : sp.dst.Covers l) : InSlot L y (pkt X y jc % 3) l := by
  obtain ⟨i, j, -, hd⟩ := hC.dst
  have hcl := Loader.rowCol_lt _ (Nat.mod_lt (y % L.block) (show 0 < 64 by decide))
  have hi := i.isLt
  have hj := j.isLt
  obtain ⟨c1, c2, c3, c4⟩ := hc
  rw [hd] at c1 c2 c3 c4
  simp only [Loader.cpAddr] at c1 c2 c3 c4
  refine ⟨l.addr - (L.sharedBase + 68608 + 32768 * (pkt X y jc % 3)), by omega, ?_⟩
  obtain ⟨s1, c, a⟩ := l
  simp only at c1 c2 c3 c4 ⊢
  simp only [Loc.mk.injEq]
  exact ⟨c1, c2, by omega⟩

/-- **A copy of a packet is before a copy of a later packet of its slot.** -/
theorem kv_copy_copy {y jc pc y' jc' pc' : Nat} {sp sp' : AsyncCopy.Spec} {l : Loc}
    (hcp : X.get (y, jc) = some ⟨pc, .copy sp⟩) (hcp' : X.get (y', jc') = some ⟨pc', .copy sp'⟩)
    (hy : Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15) (hC : LdCp L X y jc sp)
    (hy' : Prologue.warpIndex L y' = 14 ∨ Prologue.warpIndex L y' = 15)
    (hC' : LdCp L X y' jc' sp') (hcta : y / L.block = y' / L.block)
    (hs : pkt X y jc % 3 = pkt X y' jc' % 3) (hlt : pkt X y jc < pkt X y' jc')
    (hc : sp.dst.Covers l) (hca : AsyncCovers X (y, jc) (.write .copy) l)
    (hcb : AsyncCovers X (y', jc') (.write .copy) l) :
    modelCausality L X l (.async (y, jc) (.write .copy)) (.async (y', jc') (.write .copy)) := by
  set t := pkt X y jc with ht
  have hyl := Frame.lt_of_get hX hcp
  obtain ⟨c, hc12, -, -, -, hempty⟩ := kvHandoff hp hX hFw y hyl
    ⟨t % 3, Nat.mod_lt _ (by decide)⟩
  have hp1 : t / 3 + 1 + 1 ≤ okPolls (obj L y (56 + 8 * (t % 3))) ((X.tr y').take jc') := by
    have h3 := hC'.polls
    rw [← hs, ← obj_cta hcta] at h3
    rw [h3]
    omega
  obtain ⟨j, pcj, par, acq, sc, hjk, hje, hjn⟩ := nth_poll hp1
  obtain rfl := kv_empty_acq hp hX hFw hje
  obtain ⟨i, pci, spc, rank, hie, hmb, hcnt, -, hob, hdone⟩ := hempty ⟨hcta.symm, hy'⟩ hje hjn
  have hcc : c / L.block = y / L.block := hc12.2.1
  have hmb' : spc.mbar = obj L c (56 + 8 * (t % 3)) := by rw [obj_cta hcc]; exact hmb
  have hsl : InSlot L c (t % 3) l := by
    obtain ⟨off, ho, rfl⟩ := copy_slot hC hc
    exact ⟨off, ho, by rw [hcc]⟩
  obtain ⟨t', k', idx, d, sp1, acc, mask, e1, e2, hk', hR, hmma, hidx, hbl⟩ :=
    kv_release_read hp hX hFw (s := ⟨t % 3, Nat.mod_lt _ (by decide)⟩) hc12.2.2 hie hmb' hsl
  have htt : t' = t := by
    simp only at e1 e2
    rw [obj_cta hcc] at e2
    have : t' / 3 = t / 3 := by
      rw [← e2]
      exact hcnt
    omega
  subst htt
  have hcr : AsyncCovers X (c, k') (.mmaRead true idx) l := mma_covers hmma hbl
  have hW := kv_copy_read hp hX hFw hcp hy hC hR hcc.symm rfl le_rfl hca hcr
  have hRd := kv_read_copy hp hX hFw hcp' hy' hC' hR (hcta.symm.trans hcc.symm) hs.symm hlt hcr hcb
  have htr : TracksMma X (c, k') (c, i) := ⟨rfl, hk', .inl ⟨_, _, _, _, hmma⟩, spc, ⟨_, hie⟩⟩
  have hpres : X.AsyncPresent (c, k') (.mmaRead true idx) := by
    refine PairTmaRing.mmaRead_present hX (hdone _ htr) hmma hbl ?_
    have hspec : ∃ c', Tm.Spec128 sp1 c' := by
      obtain ⟨st, u, jj, ⟨h, -⟩ | ⟨h, -⟩⟩ := hR
      · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hmma
        exact ⟨_, .inl rfl, rfl, rfl⟩
      · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hmma
        exact ⟨_, .inr rfl, rfl, rfl⟩
    obtain ⟨c', hc'⟩ := hspec
    exact lt_of_lt_of_eq hidx (Tm.opBytes hc' _).symm
  exact ⟨.inl ⟨hyl, Frame.lt_of_get hX hcp', hcta⟩, hW.2.trans hpres hRd.2⟩

/-- **Two row copies of one byte are ordered, or one.** -/
theorem kv_row_row {y jc pc y' jc' pc' : Nat} {sp sp' : AsyncCopy.Spec} {l : Loc}
    (hcp : X.get (y, jc) = some ⟨pc, .copy sp⟩) (hcp' : X.get (y', jc') = some ⟨pc', .copy sp'⟩)
    (hc : sp.dst.Covers l) (hc' : sp'.dst.Covers l)
    (hca : AsyncCovers X (y, jc) (.write .copy) l)
    (hcb : AsyncCovers X (y', jc') (.write .copy) l) (hne : (y, jc) ≠ (y', jc')) :
    modelCausality L X l (.async (y, jc) (.write .copy)) (.async (y', jc') (.write .copy)) ∨
      modelCausality L X l (.async (y', jc') (.write .copy)) (.async (y, jc) (.write .copy)) := by
  obtain ⟨hy, hC⟩ := copy_row hp hX hFw (i := (y, jc)) ⟨_, hcp⟩
  obtain ⟨hy', hC'⟩ := copy_row hp hX hFw (i := (y', jc')) ⟨_, hcp'⟩
  simp only at hy hC hy' hC'
  obtain ⟨off, ho, rfl⟩ := copy_slot hC hc
  have hsl' := copy_slot hC' hc'
  obtain ⟨off', ho', hl'⟩ := hsl'
  simp only [Loc.mk.injEq, true_and] at hl'
  obtain ⟨hcta, hadd⟩ := hl'
  have h3 := Nat.mod_lt (pkt X y jc) (show 0 < 3 by decide)
  have h3' := Nat.mod_lt (pkt X y' jc') (show 0 < 3 by decide)
  have hs : pkt X y jc % 3 = pkt X y' jc' % 3 := by omega
  rcases Nat.lt_trichotomy (pkt X y jc) (pkt X y' jc') with h | h | h
  · exact .inl (kv_copy_copy hp hX hFw hcp hcp' hy hC hy' hC' hcta hs h hc hca hcb)
  · exfalso
    have hb := hp.block
    obtain ⟨i, j, hij, hd⟩ := hC.dst
    obtain ⟨i', j', hij', hd'⟩ := hC'.dst
    have hcl := Loader.rowCol_lt _ (Nat.mod_lt (y % L.block) (show 0 < 64 by decide))
    have hcl' := Loader.rowCol_lt _ (Nat.mod_lt (y' % L.block) (show 0 < 64 by decide))
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨-, -, c3, c4⟩ := hc
    obtain ⟨-, -, d3, d4⟩ := hc'
    rw [hd] at c3 c4
    rw [hd'] at d3 d4
    simp only [Loader.cpAddr] at c3 c4 d3 d4
    rw [← hs] at d3 d4
    have hcol : Loader.rowCol (y % L.block % 64) = Loader.rowCol (y' % L.block % 64) := by omega
    have hlane := Loader.rowCol_inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) hcol
    have hyy : y = y' := by
      simp only [Prologue.warpIndex, hb] at hy hy' hlane hcta
      omega
    subst hyy
    have hcnt : ((X.tr y).take jc).countP cpCopy = ((X.tr y).take jc').countP cpCopy := by
      unfold pkt at h
      omega
    exact hne (by rw [nthEv_unique (p := cpCopy) hcp rfl hcp' rfl hcnt])
  · exact .inr (kv_copy_copy hp hX hFw hcp' hcp hy' hC' hy hC hcta.symm hs.symm h hc' hcb hca)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
