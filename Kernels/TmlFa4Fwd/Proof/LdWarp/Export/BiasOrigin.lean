-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Input
public import Kernels.TmlFa4Fwd.Proof.LdWarp.TileNum
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.BiasIssue
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

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

namespace Loader

private def biasStage (tt : Fin 7) : Fin 2 := if tt.val = 2 ∨ tt.val = 3 ∨ tt.val = 5 then 1 else 0

private theorem stage_of_input : ∀ (tt : Fin 7) (c st q : Fin 2),
    (inputSite (siteOf tt c)).sharedOffset = 166912+32768*st.val+16384*q.val →
      biasStage tt = st := by decide

private def rowWord (v : V) (st : Fin 2) :=
  if st = 0 then add32 v.sc.c0 v.su.r741 else addi (add32 v.sc.c0 v.su.r741) 128

private theorem row_head_regs {w : Nat} {ent : Nat → Value} {v : V} {kk : Fin 2} {t : TState}
    (tt : Fin 7) (c : Fin 2) (h : (code p L g w ent).AtD ⟨.tc tt c,v,kk⟩ t) :
    t.regs (inputSite (siteOf tt c)).rowReg = some (.bits 32 (rowWord v (biasStage tt))) ∧
    t.regs 7169 = some (.bits 32 v.co.head) := by
  fin_cases tt <;> fin_cases c <;> exact ⟨lreg h (by lit_mem) rfl,lreg h (by lit_mem) rfl⟩

private theorem stage_row (base row : Nat) (st : Fin 2) (bound : base+row+128 < 2^32) :
    (if st=0 then add32 (W base) (W row) else addi (add32 (W base) (W row)) 128) =
      W (base+row+128*st.val) := by
  rw [add32_W (by omega)]
  fin_cases st
  · rfl
  · exact addi_W (n := 128) (by decide) (by omega)

private theorem axis_word {n : Nat} (hn : n < 2^31) :
    (BitVec.ofNat 32 (truncBits 32 (W n)).toNat).toInt = n := by
  rw [show truncBits 32 (W n) = r32 (W n) from rfl, r32_W (by omega), toNat_W (by omega),
    BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  split <;> omega

end Loader

/-- Every bias issue of this shared stage uses its chosen tile's request row and head. -/
theorem ld_bias_row_head (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    {pc a : Nat} {j : Fin 14} {org : Fin 3 → Int} {mb : Loc}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a (inputSpec p L (g / L.block) j org mb)⟩)
    {st q : Fin 2}
    (hoff : (Loader.inputSite j).sharedOffset = 166912 + 32768 * st.val + 16384 * q.val) :
    ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧
      org 1 = ((p.qOffset b + 256*(Epilogue.assignedCoordinates p b (g/L.block)).1 +
        128*st.val : Nat) : Int) ∧ org 2 = (Epilogue.assignedCoordinates p b (g/L.block)).2 := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .tensorIssue a (inputSpec p L (g / L.block) j org mb)⟩ : Event).kind ≠
    .ub f := fun f h => by cases h
  obtain ⟨b,tt,c,v,kk,n,hσ,h0,hR⟩ := LdWarp.issue_state hp hX hFw hw he
  let d : Loader.D := ⟨.tc tt c,v,kk⟩
  obtain ⟨ts, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hblk : d.site.blk = true := LdWarp.tc_blk tt c
  obtain ⟨R, bal, hP, hco, hsu, -⟩ := LdWarp.tile_inv hp hX hg hw k
    (List.getElem?_eq_some_iff.mp he).1.le b d n hσ h0 hblk
  obtain ⟨bb, hN⟩ := Loader.tile_num hp hg hP
  have hc0 : d.v.sc.c0 = W (p.qOffset bb) := by
    obtain ⟨_,fit,_,_,_⟩ := Loader.lfits_blk_of hblk (hR.2 h0).2
    simp only [Epilogue.Fits,Loader.toE,Loader.epi_blk hblk] at fit
    obtain ⟨R',bal',hC,hc0,_⟩ := fit
    obtain ⟨hPk, -, hgx, -, hbal, -, -, -, -⟩ := id hC
    obtain ⟨rfl, rfl⟩ := hP.unique hPk
    simp only [Epilogue.chosen] at hgx hbal hc0
    have hch : Epilogue.chosen d.v.sc =
        Epilogue.chosen (Epilogue.chosenD p (g / L.block) R bal) := by
      simp only [Epilogue.chosen, hgx, hbal, Epilogue.chosenD]
    rw [← hN.c0]
    exact hc0.trans (congrArg (Epilogue.qv p) hch)
  change v.sc.c0 = _ at hc0
  change v.co = _ at hco
  change v.su = _ at hsu
  obtain ⟨xc, xr, xh, mb', e1, e2, e3, hk⟩ := Loader.tc_spec hp hg hat hc hf
  simp only [Kind.tensorIssue.injEq, inputSpec, TensorCopy.Spec.mk.injEq, TensorBox.mk.injEq] at hk
  obtain ⟨_,⟨_,_,origin,base,_⟩,_⟩ := hk
  have hoff' : (Loader.inputSite (Loader.siteOf tt c)).sharedOffset =
      166912 + 32768 * st.val + 16384 * q.val := by
    have := congrArg Loc.addr base
    simp only at this
    omega
  have stage := Loader.stage_of_input tt c st q hoff'
  obtain ⟨rr,rh⟩ := Loader.row_head_regs tt c hat
  rw [stage] at rr
  rw [rr] at e2
  rw [rh] at e3
  simp only [Option.some.injEq, Value.bits.injEq, true_and] at e2 e3
  subst e2 e3
  refine ⟨bb,hN.batch,hN.lo,hN.hi,?_⟩
  rw [eq_of_heq origin]
  obtain ⟨hv1, hv2⟩ := Epilogue.assignedCoordinates_valid hp hN.lo hN.hi
  have hl := (hp.lengths bb hN.batch).1
  have hq1 := hp.qOffset_le_total (show bb + 1 ≤ p.batch by have := hN.batch; omega)
  obtain ⟨_,_,_,_,_,htq⟩ := hp.shape
  have hql : p.qLength bb = p.qOffset (bb + 1) - p.qOffset bb := rfl
  have hhd := Epilogue.heads_lt hp
  have hc2 := c.isLt
  have hst2 := st.isLt
  simp only [Loader.rowWord,hc0,hsu,hN.row,hco,hN.head]
  rw [Loader.stage_row _ _ st (by omega)]
  exact ⟨Loader.axis_word (by omega),Loader.axis_word (by omega)⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
