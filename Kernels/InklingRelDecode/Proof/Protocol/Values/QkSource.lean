-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Wrote
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Lemmas.Tcgen05.TcProgramOrder
import Lemmas.Tcgen05.TcMmaSource

@[expose] public section

/-! # The source of a QK step's accumulator is the step before it

A QK step `j` of a lane reads the cell the step `j - 1` of the same round wrote. The source of the
read is that step: any other write of the cell is a QK step of the lane between the two, and a QK
step is issued once per round (`qk_once`), so no step of the round lies between them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- Lane `g` issued QK step `j` at its position `k`. -/
def QkAt (X : Execution) (g k : Nat) (j : Fin 8) : Prop :=
  ∃ d s acc mask, X.get (g, k) = some ⟨Lib.qkIssue j, .tc (.mma d s acc mask)⟩

private theorem qk_pc_ne : ∀ j j' : Fin 8, Lib.qkIssue j ≠ Lib.pvIssue j' := by
  decide +kernel

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem poll_round_mono {g k k' : Nat} (h : k ≤ k') :
    pollRound 2462 ((X.tr g).take k) ≤ pollRound 2462 ((X.tr g).take k') :=
  (List.take_sublist_take_left h).countP_le (p := okPollAt 2462)

/-- **A QK step is the only one of its round**: two issues of step `j` in one round coincide. -/
theorem qk_unique (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {g k1 k2 : Nat} {j : Fin 8}
    (h1 : QkAt X g k1 j) (h2 : QkAt X g k2 j)
    (hr : pollRound 2462 ((X.tr g).take k1) = pollRound 2462 ((X.tr g).take k2)) : k1 = k2 := by
  obtain ⟨_, _, _, _, e1⟩ := h1
  obtain ⟨_, _, _, _, e2⟩ := h2
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := Mma.Export.qk_once hp hX hf words e1 e2 rfl h
    omega
  · exact h
  · have := Mma.Export.qk_once hp hX hf words e2 e1 rfl h
    omega

/-- **Two MMAs writing one cell are of one lane and one accumulator**, of the fixed QK/PV shape. -/
theorem mma_acc_eq (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {x y : EvId} {cell : Cell} (cx : X.MmaCell x cell) (cy : X.MmaCell y cell) :
    ∃ px dx sx ax mx py dy sy ay my, X.get x = some ⟨px, .tc (.mma dx sx ax mx)⟩ ∧
      X.get y = some ⟨py, .tc (.mma dy sy ay my)⟩ ∧ x.1 = y.1 ∧ dx = dy ∧
      sx.descriptor = sy.descriptor ∧ sx.lowCta = sy.lowCta ∧ sx.highCta = sy.highCta ∧
      sx.descriptor.m = 64 ∧ sx.descriptor.group = .one ∧ sx.descriptor.ws = false ∧
      dx / 2 ^ 16 = 0 := by
  obtain ⟨px, dx, sx, ax, mx, hx, ctx, dlx, dhx, lox, hix, kx⟩ := mma_write_cell hp hX hf base cx
  obtain ⟨py, dy, sy, ay, my, hy, cty, dly, dhy, loy, hiy, ky⟩ := mma_write_cell hp hX hf base cy
  have thr : x.1 = y.1 := mma_thread hp hX hf hx hy (ctx.symm.trans cty)
  have hd : dx = dy ∧ sx.descriptor = sy.descriptor ∧ sx.descriptor.m = 64 ∧
      sx.descriptor.group = .one ∧ sx.descriptor.ws = false ∧ dx < 512 := by
    rcases kx with ⟨-, -, hdx, ex⟩ | ⟨-, -, hdx, ex⟩ <;>
      rcases ky with ⟨-, -, hdy, ey⟩ | ⟨-, -, hdy, ey⟩ <;> rw [ex, ey] <;>
      first | exact ⟨by omega, rfl, rfl, rfl, rfl, by omega⟩ | (exfalso; omega)
  obtain ⟨hdd, hdesc, hm, hg, hw, hlt⟩ := hd
  exact ⟨px, dx, sx, ax, mx, py, dy, sy, ay, my, hx, hy, thr, hdd, hdesc,
    by rw [lox, loy, thr], by rw [hix, hiy, thr], hm, hg, hw, Nat.div_eq_of_lt (by omega)⟩

/-- **Two MMAs of one CTA writing a cell, the first earlier in the lane, are ordered writes.** -/
theorem mma_wb (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {x y : EvId} {cell : Cell} (cx : X.MmaCell x cell) (cy : X.MmaCell y cell) :
    x.1 = y.1 ∧ (x.2 < y.2 → WriteBefore L X x y) := by
  obtain ⟨px, dx, sx, ax, mx, py, dy, sy, ay, my, hx, hy, thr, hd, hdesc, hlo, hhi, -⟩ :=
    mma_acc_eq hp hX hf base cx cy
  refine ⟨thr, fun hlt =>
    .inl (Before.of_mma_po ⟨_, hx⟩ ⟨_, hy⟩ (Frame.lt_of_get hX hx) thr hlt ?_)⟩
  exact ⟨hd, by rw [hdesc], by rw [hdesc], hlo, hhi⟩

/-- **A write of a cell before another, both MMAs of a CTA, is earlier in the lane.** -/
theorem mma_wb_lt (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) (hG : SyncGuarded L kernel X)
    {x y : EvId} {cell : Cell} (cx : X.MmaCell x cell) (cy : X.MmaCell y cell)
    (hwb : WriteBefore L X x y) : x.2 < y.2 := by
  obtain ⟨thr, fwd⟩ := mma_wb hp hX hf base cx cy
  obtain ⟨-, bwd⟩ := mma_wb hp hX hf base cy cx
  rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
  · exact h
  · have e : x = y := Prod.ext thr h
    subst e
    exact (writeBefore_asymm hX hG hwb hwb).elim
  · exact (writeBefore_asymm hX hG hwb (bwd h)).elim

/-- A Tensor Memory write by an MMA event is an MMA write. -/
theorem mma_of_write {x : EvId} {cell : Cell} {pc d s acc mask}
    (hx : X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩) (hw : TmemWrite L X x cell) :
    X.MmaCell x cell := by
  rcases hw with mc | ⟨a, v, sh, i, ⟨pc', hst⟩, -⟩ | ⟨c, cta, ix, ln, ⟨pc', hcp⟩, -⟩ |
    ⟨sp, ⟨pc', hsh⟩, -⟩
  · exact mc
  · cases get_tc_inj hx hst
  · cases get_tc_inj hx hcp
  · cases get_tc_inj hx hsh

/-- **The source of a QK step's accumulator read is the step before it.** -/
theorem qk_source (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) (hG : SyncGuarded L kernel X)
    {g kp : Nat} {cell : Cell} {src : EvId} {d s mask} {j j' : Fin 8}
    (he : X.get (g, kp) = some ⟨Lib.qkIssue j, .tc (.mma d s true mask)⟩)
    (hrd : X.MmaReadCell (g, kp) cell) (hs : ReadSource L X .acc src (g, kp) cell)
    (hsm : X.MmaCell src cell) (hj' : j'.val + 1 = j.val) :
    ∃ kR, src = (g, kR) ∧ QkAt X g kR j' ∧
      pollRound 2462 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take kp) := by
  have words : RoleBytes L X := fun h => Shared.role_bytes hp hX h
  obtain ⟨kR, ltR, ⟨dR, sR, aR, mR, getR⟩, qR, wr, wb⟩ :=
    qk_prev_step hp hX hf hu base hrd he rfl j' hj'
  have hmR : X.MmaCell (g, kR) cell := mma_of_write getR wr
  have hmp : X.MmaCell (g, kp) cell := mma_read_write hp hX hf base hrd
  obtain ⟨hne, -, hsw, hmaster, -⟩ := readSource_acc.mp hs
  rcases hmaster (g, kR) wr with h | h | h | h
  · exact ⟨kR, h.symm, ⟨dR, sR, aR, mR, getR⟩, qR⟩
  · exact absurd (congrArg Prod.snd h) (by simp; omega)
  · exfalso
    have lt1 := mma_wb_lt hp hX hf base hG hmR hsm h
    have lt2 := mma_wb_lt hp hX hf base hG hsm hmp hsw
    obtain ⟨hthr, -⟩ := mma_wb hp hX hf base hsm hmp
    obtain ⟨ks, hks⟩ : ∃ ks, src = (g, ks) := ⟨src.2, Prod.ext hthr rfl⟩
    subst hks
    simp only at lt1 lt2
    obtain ⟨pcs, ds, ss, as, ms, hes, -, dls, dhs, -, -, kind⟩ := mma_write_cell hp hX hf base hsm
    obtain ⟨pcp, dp, sp, ap, mp, hep, -, dlp, dhp, -, -, kindp⟩ := mma_write_cell hp hX hf base hmp
    have hpe : pcp = Lib.qkIssue j := (Event.mk.inj (Option.some.inj (hep.symm.trans he))).1
    obtain ⟨j2, hpcs⟩ : ∃ j2, pcs = Lib.qkIssue j2 := by
      rcases kindp with ⟨-, -, hdp, -⟩ | ⟨j3, hpv, -⟩
      · rcases kind with ⟨j2, h2, -⟩ | ⟨-, -, hd, -⟩
        · exact ⟨j2, h2⟩
        · exfalso
          omega
      · exact absurd (hpe.symm.trans hpv) (qk_pc_ne _ _)
    have rks : pollRound 2462 ((X.tr g).take ks) = pollRound 2462 ((X.tr g).take kp) := by
      have := poll_round_mono (X := X) (g := g) lt1.le
      have := poll_round_mono (X := X) (g := g) lt2.le
      omega
    have hqs : QkAt X g ks j2 := ⟨ds, ss, as, ms, by rw [← hpcs]; exact hes⟩
    have hqp : QkAt X g kp j := ⟨d, s, true, mask, he⟩
    have hqr : QkAt X g kR j' := ⟨dR, sR, aR, mR, getR⟩
    rcases Nat.lt_trichotomy j2.val j.val with h1 | h1 | h1
    · rcases Nat.lt_or_ge j2.val j'.val with h2 | h2
      · obtain ⟨kk, ltk, d3, s3, a3, m3, getk, qk⟩ :=
          Mma.Export.qk_prior hp hX hf words hu getR rfl j2 h2
        have := qk_unique hp hX hf words ⟨d3, s3, a3, m3, getk⟩ hqs (by omega)
        omega
      · have : j2 = j' := Fin.ext (by omega)
        subst this
        have := qk_unique hp hX hf words hqr hqs (by omega)
        omega
    · have : j2 = j := Fin.ext h1
      subst this
      have := qk_unique hp hX hf words hqs hqp rks
      omega
    · obtain ⟨kk, ltk, d3, s3, a3, m3, getk, qk⟩ :=
        Mma.Export.qk_prior hp hX hf words hu hes hpcs j h1
      have := qk_unique hp hX hf words ⟨d3, s3, a3, m3, getk⟩ hqp (by omega)
      omega
  · exfalso
    exact writeBefore_asymm hX hG wb (.inl h)
