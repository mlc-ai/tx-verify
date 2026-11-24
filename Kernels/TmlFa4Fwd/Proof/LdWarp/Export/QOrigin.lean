-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Input
public import Kernels.TmlFa4Fwd.Proof.LdWarp.TileNum
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.TileInv
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Lib.Start
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSite
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.TcSpec
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Lemmas.Flow.Arith32WordW
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The boxes of the Q copies

A Q copy of a loader lane reads the box of its tile: the 64 columns of its half, the 128 rows of its
stage after the tile's first row, and the tile's head (`ld_q_origin`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

namespace Loader

/-- The box of a Q copy of stage `st` and half `q`, of the words of a lane's state. -/
private def qWords (v : V) (st q : Fin 2) : BitVec 64 × BitVec 64 × BitVec 64 :=
  (W (64 * q.val), if st = 0 then add32 v.sc.c0 v.su.r741
    else addi (add32 v.sc.c0 v.su.r741) 128, v.co.head)

/-- The stage of a Q group. -/
private def qGrp (st : Fin 2) : Fin 7 := if st = 0 then 0 else 2

set_option maxHeartbeats 4000000 in
private theorem q_regs {w : Nat} {ent : Nat → Value} {v : V} {kk : Fin 2} {t : TState}
    (st q : Fin 2) (h : (code p L g w ent).AtD ⟨.tc (qGrp st) q, v, kk⟩ t) :
    t.regs (inputSite (siteOf (qGrp st) q)).colReg = some (.bits 32 (qWords v st q).1) ∧
    t.regs (inputSite (siteOf (qGrp st) q)).rowReg = some (.bits 32 (qWords v st q).2.1) ∧
    t.regs 7169 = some (.bits 32 (qWords v st q).2.2) := by
  fin_cases st <;> fin_cases q <;>
    exact ⟨lreg h (by lit_mem) rfl, lreg h (by lit_mem) rfl, lreg h (by lit_mem) rfl⟩

private theorem origin_W {c r h : Nat} (hc : c < 2 ^ 31) (hr : r < 2 ^ 31) (hh : h < 2 ^ 31) :
    boxOrigin (W c) (W r) (W h) = ![(c : Int), (r : Int), (h : Int)] := by
  have key : ∀ n : Nat, n < 2 ^ 31 → (BitVec.ofNat 32 (truncBits 32 (W n)).toNat).toInt = n := by
    intro n hn
    rw [show truncBits 32 (W n) = r32 (W n) from rfl, r32_W (by omega), toNat_W (by omega),
      BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    split <;> omega
  funext i
  fin_cases i
  · exact key c hc
  · exact key r hr
  · exact key h hh

private theorem q_site : ∀ (tt : Fin 7) (c st q : Fin 2),
    (inputSite (siteOf tt c)).sharedOffset = 3072 + 32768 * st.val + 16384 * q.val →
      tt = qGrp st ∧ c = q := by decide

end Loader

/-- **The box of a Q copy.** -/
theorem ld_q_origin (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    {pc a : Nat} {j : Fin 14} {org : Fin 3 → Int} {mb : Loc}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a (inputSpec p L (g / L.block) j org mb)⟩)
    {st q : Fin 2}
    (hoff : (Loader.inputSite j).sharedOffset = 3072 + 32768 * st.val + 16384 * q.val) :
    ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧
      org = ![((64 * q.val : Nat) : Int),
        ((p.qOffset b + 256 * (Epilogue.assignedCoordinates p b (g / L.block)).1 +
          128 * st.val : Nat) : Int),
        (((Epilogue.assignedCoordinates p b (g / L.block)).2 : Nat) : Int)] := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .tensorIssue a (inputSpec p L (g / L.block) j org mb)⟩ : Event).kind ≠
    .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_no_tensor hev hi.2).elim
  obtain ⟨-, -, h3, -⟩ := Loader.copy_site hev hub
  obtain ⟨tt, c, hs⟩ := h3.mp ⟨_, _, rfl⟩
  obtain ⟨ts, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hblk : d.site.blk = true := by rw [hs]; fin_cases tt <;> rfl
  obtain ⟨R, bal, hP, hco, hsu, -⟩ := LdWarp.tile_inv hp hX hg hw k
    (List.getElem?_eq_some_iff.mp he).1.le b d n hσ h0 hblk
  obtain ⟨bb, hN⟩ := Loader.tile_num hp hg hP
  have hc0 : d.v.sc.c0 = W (p.qOffset bb) := by
    have hF := (Loader.lfits_blk_of hblk (hR.2 h0).2).2.1
    have hep := Loader.epi_blk hblk
    simp only [Epilogue.Fits, Loader.toE, hep] at hF
    obtain ⟨R', bal', hC, hc0, -⟩ := hF
    obtain ⟨hPk, -, hgx, -, hbal, -, -, -, -⟩ := id hC
    obtain ⟨rfl, rfl⟩ := hP.unique hPk
    simp only [Epilogue.chosen] at hgx hbal hc0
    have hch : Epilogue.chosen d.v.sc =
        Epilogue.chosen (Epilogue.chosenD p (g / L.block) R bal) := by
      simp only [Epilogue.chosen, hgx, hbal, Epilogue.chosenD]
    rw [← hN.c0]
    exact hc0.trans (congrArg (Epilogue.qv p) hch)
  obtain ⟨site, v, kk⟩ := d
  simp only at hs hc0 hco hsu
  subst hs
  obtain ⟨xc, xr, xh, mb', e1, e2, e3, hk⟩ := Loader.tc_spec hp hg hat hc hf
  simp only [Kind.tensorIssue.injEq, inputSpec, TensorCopy.Spec.mk.injEq, TensorBox.mk.injEq] at hk
  obtain ⟨-, hbox, -⟩ := hk
  have hoff' : (Loader.inputSite (Loader.siteOf tt c)).sharedOffset =
      3072 + 32768 * st.val + 16384 * q.val := by
    have := congrArg Loc.addr hbox.2.2.2.1
    simp only at this
    omega
  obtain ⟨rfl, rfl⟩ := Loader.q_site tt c st q hoff'
  obtain ⟨r1, r2, r3⟩ := Loader.q_regs st c hat
  rw [r1] at e1
  rw [r2] at e2
  rw [r3] at e3
  simp only [Option.some.injEq, Value.bits.injEq, true_and] at e1 e2 e3
  subst e1 e2 e3
  refine ⟨bb, hN.batch, hN.lo, hN.hi, ?_⟩
  rw [eq_of_heq hbox.2.2.1]
  obtain ⟨hv1, hv2⟩ := Epilogue.assignedCoordinates_valid hp hN.lo hN.hi
  have hl := (hp.lengths bb hN.batch).1
  have hq1 := hp.qOffset_le_total (show bb + 1 ≤ p.batch by have := hN.batch; omega)
  have htq := hp.shape.2.2.2.2.2
  have hql : p.qLength bb = p.qOffset (bb + 1) - p.qOffset bb := rfl
  have hhd := Epilogue.heads_lt hp
  have hc2 := c.isLt
  have hst2 := st.isLt
  simp only [Loader.qWords, hc0, hsu, hN.row, hco, hN.head]
  have hrow : (if st = 0 then add32 (W (p.qOffset bb))
      (W (256 * (Epilogue.assignedCoordinates p bb (g / L.block)).1))
      else addi (add32 (W (p.qOffset bb))
        (W (256 * (Epilogue.assignedCoordinates p bb (g / L.block)).1))) 128) =
      W (p.qOffset bb + 256 * (Epilogue.assignedCoordinates p bb (g / L.block)).1 +
        128 * st.val) := by
    rw [add32_W (by omega)]
    split
    · rename_i h; subst h; rfl
    · rename_i h
      have : st = 1 := by omega
      subst this
      exact addi_W (n := 128) (by decide) (by omega)
  rw [hrow]
  exact Loader.origin_W (by omega) (by omega) (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof
