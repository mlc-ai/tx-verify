-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Order
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
public import Lemmas.Protocol.RegionOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasRd
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageRead
import Lemmas.Order.OrderBaseCausality
import Lemmas.Order.OrderWaits
import Lemmas.Protocol.CountNth
import Lemmas.Protocol.PollIndex
import Lemmas.Tensor.TensorCompleteConsistentRead
import Lemmas.Tensor.TensorTransfer
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias stages are ordered

A byte of box `q` of a bias stage is written by the copies of the stage's lane with `2 u + q`
earlier ones and read by the stage's lanes in round `u`. A copy of round `u` is observed by every
stage lane's poll `u`, which is before the lane's reads of the rounds from `u` on and, through the
stage barrier, before the copies of the later rounds; a read of round `u` is before the lane's proxy
fence and stage barrier of round `u`, hence before the copies of the later rounds
(`bias_ordered`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A byte of the bias stages. -/
def InBias (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 166912 ≤ l.addr ∧ l.addr < L.sharedBase + 232448

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A copy of round `u`, observed by a stage lane.** -/
theorem bias_copy_done {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h) {i pc al k : Nat}
    {s : TensorCopy.Spec} (he : X.get (tmaLane L X g, i) = some ⟨pc, .tensorIssue al s⟩)
    (hm : s.mbar = bF L g st)
    (hk : ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) / 2 + 1 ≤
      okPolls (bF L g st) ((X.tr h).take k)) (x y z : Nat) :
    ∃ jw, jw < k ∧ okPolls (bF L g st) ((X.tr h).take jw) =
        ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) / 2 ∧
      (X.get (h, jw)).bind Event.acc = none ∧
      AsyncFinished L X (tmaLane L X g, i) (.write (.load x y z)) (h, jw) := by
  have hB := tmaBytes hp hX hFw
  set N := ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) with hN
  have hty := (tmaLane_in (X := X) hp g).1
  obtain ⟨jw, pcw, par, acq, sc, hjk, hw, hwo⟩ := Poll.exists_nth hk
  have hacq : acq = true := by
    obtain ⟨-, hu2⟩ := bias_use hp hX hFw st hw rfl (fun _ h => by cases h)
    rcases hu2 with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, _, hk, _⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, -, -, hacq, -⟩ := hk
      exact hacq
    · cases hk
    · cases hk
  subst hacq
  obtain ⟨i1, pci, al1, sp, he1, hm1, hc1, -, hW⟩ := bias_observes hp hX hFw hB hh hw hwo
    ⟨N % 2, Nat.mod_lt _ (by decide)⟩
  have hii : i1 = i := by
    have h1 := nthEv_eq (p := issuesTo (bF L g st)) he1 (by simp [issuesTo, hm1])
    have h2 := nthEv_eq (p := issuesTo (bF L g st)) he (by simp [issuesTo, hm])
    rw [← h1, ← h2, hc1, ← hN]
    congr 1
    simp only
    omega
  subst hii
  refine ⟨jw, hjk, hwo, by simp [hw, Event.acc], ?_⟩
  obtain ⟨-, hU⟩ := id hW
  obtain ⟨ii, jj, r, w, phase, hrec, hid, -⟩ := hU
  have hpres := object_record_present hX.tma (List.mem_of_getElem? hrec)
  rw [hid] at hpres
  obtain ⟨o, ho, hn⟩ := id hpres
  obtain ⟨⟨addr, pco, hio⟩, -⟩ := hX.tensor _ o ho
  have hos : o.spec = sp := by
    rw [he1] at hio
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
    exact hio.2.2.symm
  refine .inr ⟨sc, ⟨_, _, ⟨rfl, o, addr, ho, ⟨pco, hio⟩, by rw [hos]; exact hm1, hn⟩, hW⟩, ?_⟩
  exact ScopesMeet.of_sameCta ⟨Frame.lt_of_get hX he1, hh.1, hty.trans hh.2.1.symm⟩

/-- **A copy of a later round follows a stage lane's event before its stage-barrier event.** -/
theorem bias_next {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h) {i pc al u : Nat}
    {s : TensorCopy.Spec} (he : X.get (tmaLane L X g, i) = some ⟨pc, .tensorIssue al s⟩)
    (hm : s.mbar = bF L g st)
    (hu : u < ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) / 2) :
    ∃ ib pcb, X.get (h, ib) = some ⟨pcb, .bar (stageId st.val) (some 128) .sync⟩ ∧
      barOrd X h ib (stageId st.val) = u ∧
      ∀ e < ib, baseCausality L X (h, e) (tmaLane L X g, i) := by
  have hb' := (tma_copy hp hX hFw (g := g) (b_tmaOff st) he hm).2
  rw [bE_eq] at hb'
  refine bias_cause hp hX hFw (tmaBytes hp hX hFw) hh (j := u)
    (by have := len_of_get he; simpa using this) ?_
  change ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) + 1 ≤
    2 * okPolls (bE L g st) _ at hb'
  omega

omit hp hX hFw in
theorem cover_load {i : EvId} {pc al : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue al s⟩) {x y z : Nat} {l : Loc}
    (hl : TensorCopy.writeLoc s x y z = some l) : AsyncCovers X i (.write (.load x y z)) l :=
  ⟨{ loc := l, size := 1 }, true, ⟨rfl, s, al, ⟨pc, he⟩, hl, rfl⟩, ⟨rfl, rfl, le_rfl, by simp⟩⟩

/-- **The accesses of a byte of the bias stages.** -/
theorem bias_cases {r : Ref} {a : Acc} {w : Bool} {l : Loc} (hi : X.Intent r a w)
    (hc : a.Covers l) (hl : InBias L l) :
    (∃ i pc al s x y z, r = .async i (.write (.load x y z)) ∧ w = true ∧
      X.get i = some ⟨pc, .tensorIssue al s⟩ ∧ TensorCopy.writeLoc s x y z = some l) ∨
    ∃ h k pc bs, r = .thread (h, k) ∧ w = false ∧ Prologue.warpIndex L h < 8 ∧
      X.get (h, k) = some ⟨pc, .rd a bs⟩ ∧ Softmax.BiasAt L h a := by
  obtain ⟨hl0, hl1, hl2⟩ := hl
  have hs : a.loc.space = .shared := hc.1.symm.trans hl0
  have hcr := hc
  obtain ⟨-, -, h1, h2⟩ := hcr
  have hA := sh_intent hp hX hFw hi hs
  cases hA with
  | @tmaWr g k pc al sp x y z a hw he hz hloc hcta j hlo hhi =>
    refine .inl ⟨_, pc, al, sp, x, y, z, rfl, rfl, he, ?_⟩
    rw [hloc]
    obtain ⟨sp1, ct1, ad1⟩ := l
    obtain ⟨⟨sp2, ct2, ad2⟩, n, e1, e2, e3, e4⟩ := a
    obtain ⟨c1, c2, c3, c4⟩ := hc
    simp only at hz c1 c2 c3 c4 ⊢
    congr 1
    simp only [Loc.mk.injEq]
    exact ⟨c1.symm, c2.symm, by omega⟩
  | biasRd hw h =>
    rcases hi with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨_, -, h0⟩ | ⟨o, n, pc, he⟩
    · exact .inr ⟨_, _, pc, bs, rfl, rfl, hw, he, h⟩
    · cases h0
    · exact (no_rmw hX he).elim
  | allocWr hw h | allocRd hw h =>
    obtain ⟨hz, hl⟩ := h
    rw [hl] at h1 h2; simp only at h1 h2; omega
  | @statWr g k a hw h =>
    obtain ⟨hz, n, hn, hl⟩ := h
    have hst : Softmax.stN L g ≤ 1 := by unfold Softmax.stN; split <;> omega
    have := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
    rw [hl] at h2; simp only at h2; omega
  | @statRd g k a hw hw1 n st h =>
    have := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
    have hn := n.isLt
    have hst := st.isLt
    obtain ⟨hz, hl⟩ := h
    rw [hl] at h2; simp only [Correction.rowN] at h2; omega
  | @fstWr g k a hw hw1 st h =>
    obtain ⟨hz, q, hq, w, hw', hl⟩ := h
    have := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
    have hst := st.isLt
    rw [hl] at h2; simp only [Correction.rowN] at h2; omega
  | @rowCp g k pc sp _ _ h =>
    obtain ⟨i, j, -, hl⟩ := h.dst
    have hcl := Loader.rowCol_lt _ (Nat.mod_lt (g % L.block) (show 0 < 64 by decide))
    have hi := i.isLt
    have hj := j.isLt
    have h3 := Nat.mod_lt (pkt X g k) (show 0 < 3 by decide)
    rw [hl] at h2; simp only [Loader.cpAddr] at h2; omega
  | mmaA hst _ hz ho hl => rw [hl] at h2; simp only at h2; omega
  | @mmaB _ _ _ _ _ _ _ _ t hst _ hz ho hl =>
    have h3 := Nat.mod_lt t (show 0 < 3 by decide)
    rw [hl] at h2; simp only at h2; omega
  | storeRd _ _ _ _ st bx _ hlo hhi =>
    have := st.isLt
    have := bx.isLt
    obtain ⟨-, -, c3, c4⟩ := hc
    omega

/-- **The bias window is written only by the tensor copies.** -/
theorem biasWrites : BiasWrites L X := by
  intro w a bs l hw hc hs h1 h2
  rcases bias_cases hp hX hFw hw.intent hc ⟨hs, h1, h2⟩ with
    ⟨i, -, -, -, x, y, z, rfl, -⟩ | ⟨_, _, _, _, -, h, -⟩
  · exact ⟨i, x, y, z, rfl⟩
  · cases h

/-- **A copy and a read of one byte.** -/
theorem bias_copy_read {st : Fin 2} {h k i pc pc' al : Nat} {s : TensorCopy.Spec} {a : Acc}
    {bs : List (Option Byte)} {x y z : Nat} {l : Loc} (hh : SoftIn L g st.val h)
    (hl : InBias L l) (hcta : l.cta = g / L.block)
    (he : X.get (tmaLane L X g, i) = some ⟨pc, .tensorIssue al s⟩)
    (hm : s.mbar = bF L g st) (hw : TensorCopy.writeLoc s x y z = some l)
    (hr : X.get (h, k) = some ⟨pc', .rd a bs⟩) (hra : a.Covers l) :
    modelCausality L X l (.async (tmaLane L X g, i) (.write (.load x y z))) (.thread (h, k)) ∨
      modelCausality L X l (.thread (h, k)) (.async (tmaLane L X g, i) (.write (.load x y z))) := by
  have hkl : k < (X.tr h).length := by have := len_of_get hr; simpa using this
  have hty := (tmaLane_in (X := X) hp g).1
  have hstg : Prologue.warpIndex L h / 4 = st.val := by
    have hh' := hh
    obtain ⟨-, -, -, hs⟩ := hh'
    exact hs
  have hp1 := soft_bias_rd hp hX hFw hh.2.2.1 hr (hra.1.symm.trans hl.1)
  have hso : sobj L h 320 = bF L g st := by
    rw [sobj, obj_cta hh.2.1, hstg]
    simp only [bF]
    congr 1
    omega
  rw [hso, hstg] at hp1
  set N := ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) with hN
  set u := ((X.tr h).take k).countP (Execution.isBarId (stageId st.val)) with hu
  by_cases hle : N / 2 ≤ u
  · left
    obtain ⟨jw, hjk, -, hna, hfin⟩ := bias_copy_done hp hX hFw hh he hm (k := k) (by omega) x y z
    exact ⟨cover_load he hw, (h, jw), hfin,
      .inl (.single (.inl (po_of_source_not_access rfl hjk hkl hna)))⟩
  · right
    obtain ⟨ib, pcb, hib, hord, hcause⟩ := bias_next hp hX hFw hh he hm (u := u) (by omega)
    have hkb : k < ib := by
      by_contra hge
      rcases Nat.lt_or_ge ib k with hlt2 | hge2
      · have h1 : ((X.tr h).take (ib + 1)).countP (Execution.isBarId (stageId st.val)) =
            ((X.tr h).take ib).countP (Execution.isBarId (stageId st.val)) + 1 := by
          rw [List.take_add_one, show (X.tr h)[ib]? = _ from hib, List.countP_append]
          simp [Execution.isBarId]
        have h2 := (List.take_sublist_take_left (l := X.tr h)
          (show ib + 1 ≤ k by omega)).countP_le (p := Execution.isBarId (stageId st.val))
        simp only [barOrd] at hord
        omega
      · have : ib = k := by omega
        subst this
        rw [hr] at hib
        cases hib
    obtain ⟨fi, pcf, hfi, hf⟩ := soft_stage_fence hp hX hFw hh.2.2.1
      (show stageId st.val = 11 ∨ stageId st.val = 12 by
        have := st.isLt; unfold stageId; omega) hib
    have hkf : k < fi := by
      rcases Nat.lt_or_ge k fi with h1 | h1
      · exact h1
      · have : k = fi := by omega
        subst this
        rw [hr] at hf
        cases hf
    have hfl : fi < (X.tr h).length := by have := len_of_get hf; simpa using this
    refine ⟨cover_load he hw, .inl ⟨(h, fi), some (.shared .cta), none, ⟨pcf, hf⟩, hh.1,
      ⟨hl.1, hcta.trans hh.2.1.symm⟩,
      ⟨hh.1, Frame.lt_of_get hX he, by simp only [hty, hh.2.1]⟩, ?_, hcause fi (by omega)⟩⟩
    refine .single (.inl ⟨rfl, hkf, hfl, fun hsa => ?_⟩)
    have := hsa.1
    rw [hf] at this
    simp [Event.acc] at this

/-- **The bias stages are ordered.** -/
theorem bias_ordered : ConflictsOrdered L X (InBias L) := by
  intro e f a b l hcon ha hb' hl
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have hB := hp.block
  -- the box of the byte
  obtain ⟨st, q, hlo, hhi⟩ : ∃ st q : Fin 2,
      L.sharedBase + (166912 + 32768 * st.val + 16384 * q.val) ≤ l.addr ∧
      l.addr < L.sharedBase + (166912 + 32768 * st.val + 16384 * q.val) + 16384 := by
    obtain ⟨-, h1, h2⟩ := hl
    refine ⟨⟨(l.addr - L.sharedBase - 166912) / 32768, by omega⟩,
      ⟨(l.addr - L.sharedBase - 166912) / 16384 % 2, by omega⟩, ?_, ?_⟩ <;> simp only <;> omega
  set g := l.cta * L.block with hg
  have hcta : l.cta = g / L.block := by rw [hg, hB]; omega
  have hcopy : ∀ {i pc al s x y z}, X.get i = some ⟨pc, .tensorIssue al s⟩ →
      TensorCopy.writeLoc s x y z = some l → ∃ c, i = (tmaLane L X g, c) ∧ s.mbar = bF L g st ∧
      ((X.tr (tmaLane L X g)).take c).countP (issuesTo (bF L g st)) % 2 = q.val := by
    intro i pc al s x y z hi hwl
    obtain ⟨h1, h2, h3, -⟩ := bias_writer hp hX hFw (g := g) (st := st) (q := q) hi hwl hcta hlo hhi
    obtain ⟨y0, c⟩ := i
    simp only at h1 h3
    subst h1
    exact ⟨c, rfl, h2, h3⟩
  have hread : ∀ {h k pc bs} {ar : Acc}, Prologue.warpIndex L h < 8 →
      X.get (h, k) = some ⟨pc, .rd ar bs⟩ → Softmax.BiasAt L h ar → ar.Covers l →
      SoftIn L g st.val h := by
    intro h k pc bs ar hw8 hr hA hcv
    obtain ⟨hz, hsp, hc, h1, h2⟩ := hA
    obtain ⟨-, c2, c3, c4⟩ := hcv
    refine ⟨Frame.lt_of_get hX hr, by rw [← hcta, c2, hc], hw8, ?_⟩
    have hq := q.isLt
    have hst := st.isLt
    simp only [Softmax.stN, Prologue.warpIndex, hB] at h1 h2 hw8 ⊢
    split at h1 <;> split at h2 <;> omega
  rcases bias_cases hp hX hFw he ha hl with ⟨i, pc, al, s, x, y, z, rfl, rfl, g1, w1⟩ |
    ⟨h, k, pc, bs, rfl, rfl, v1, g1, r1⟩ <;>
  rcases bias_cases hp hX hFw hf hb' hl with ⟨i', pc', al', s', x', y', z', rfl, rfl, g2, w2⟩ |
    ⟨h', k', pc', bs', rfl, rfl, v2, g2, r2⟩
  · -- two copies
    obtain ⟨c, rfl, m1, p1⟩ := hcopy g1 w1
    obtain ⟨c', rfl, m2, p2⟩ := hcopy g2 w2
    have key : ∀ {c c' pc pc' al al' s s' x y z x' y' z'},
        X.get (tmaLane L X g, c) = some ⟨pc, .tensorIssue al s⟩ → s.mbar = bF L g st →
        X.get (tmaLane L X g, c') = some ⟨pc', .tensorIssue al' s'⟩ → s'.mbar = bF L g st →
        TensorCopy.writeLoc s x y z = some l → TensorCopy.writeLoc s' x' y' z' = some l →
        ((X.tr (tmaLane L X g)).take c).countP (issuesTo (bF L g st)) / 2 <
          ((X.tr (tmaLane L X g)).take c').countP (issuesTo (bF L g st)) / 2 →
        modelCausality L X l (.async (tmaLane L X g, c) (.write (.load x y z)))
          (.async (tmaLane L X g, c') (.write (.load x' y' z'))) := by
      intro c c' pc pc' al al' s s' x y z x' y' z' e1 m1 e2 m2 w1 w2 hlt
      have hst := st.isLt
      have hty := (tmaLane_in (X := X) hp g).1
      have hgl := Frame.lt_of_get hX e1
      have hh : SoftIn L g st.val (biasLane L (g / L.block) st.val 0) := by
        have hb0 : biasLane L (g / L.block) st.val 0 / L.block = g / L.block ∧
            Prologue.warpIndex L (biasLane L (g / L.block) st.val 0) = 4 * st.val := by
          simp only [biasLane, Prologue.warpIndex, hB]
          have : ((0 : Fin 4) : Nat) = 0 := rfl
          constructor <;> omega
        refine ⟨thread_lt_of_cta hgl (hb0.1.trans hty.symm), hb0.1, by omega, by omega⟩
      obtain ⟨ib, pcb, hib, hord, hcause⟩ := bias_next hp hX hFw hh e2 m2 hlt
      have hpb := bias_poll_before hp hX hFw hh hib hord
      obtain ⟨jw, hjk, -, -, hfin⟩ := bias_copy_done hp hX hFw hh e1 m1 (k := ib) (by omega) x y z
      exact ⟨.inl ⟨hgl, hgl, rfl⟩, .direct ⟨cover_load e1 w1, cover_load e2 w2,
        .inl ⟨_, hfin, hcause jw hjk⟩⟩⟩
    rcases Nat.lt_trichotomy
      (((X.tr (tmaLane L X g)).take c).countP (issuesTo (bF L g st)) / 2)
      (((X.tr (tmaLane L X g)).take c').countP (issuesTo (bF L g st)) / 2) with h | h | h
    · exact .inl (key g1 m1 g2 m2 w1 w2 h)
    · exfalso
      have hcc : c = c' := by
        have h1 := nthEv_eq (p := issuesTo (bF L g st)) g1 (by simp [issuesTo, m1])
        have h2 := nthEv_eq (p := issuesTo (bF L g st)) g2 (by simp [issuesTo, m2])
        rw [← h1, ← h2]
        congr 1
        omega
      subst hcc
      rw [g1] at g2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at g2
      obtain ⟨-, -, rfl⟩ := g2
      obtain ⟨s1, hs1, hl1⟩ := Option.map_eq_some_iff.mp w1
      obtain ⟨s2, hs2, hl2⟩ := Option.map_eq_some_iff.mp w2
      have hadd := congrArg Loc.addr (hl1.trans hl2.symm)
      have hslot : s1 = s2 := TensorTransfer.sharedByte_injective _ _ hadd
      obtain ⟨a1, a2, a3⟩ := TensorCopy.slotAt_coordinates hs1
      obtain ⟨b1, b2, b3⟩ := TensorCopy.slotAt_coordinates hs2
      subst hslot
      exact hne (by rw [← a1, ← a2, ← a3, ← b1, ← b2, ← b3])
    · exact .inr (key g2 m2 g1 m1 w2 w1 h)
  · obtain ⟨c, rfl, m1, -⟩ := hcopy g1 w1
    exact bias_copy_read hp hX hFw (hread v2 g2 r2 hb') hl hcta g1 m1 w1 g2 hb'
  · obtain ⟨c, rfl, m2, -⟩ := hcopy g2 w2
    exact (bias_copy_read hp hX hFw (hread v1 g1 r1 ha) hl hcta g2 m2 w2 g1 ha).symm
  · rcases hw with h | h <;> cases h

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
