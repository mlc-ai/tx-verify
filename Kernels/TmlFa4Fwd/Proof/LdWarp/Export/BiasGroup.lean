-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.BiasGap
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.BiasColumn
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Input
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAlt
import Kernels.TmlFa4Fwd.Proof.LdWarp.TileInv
import Kernels.TmlFa4Fwd.Proof.LdWarp.BiasIssue
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.Start
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSite
import Lemmas.Kernel.FrameU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow PTX.Proof
set_option maxRecDepth 20000

/-- The signed origin column of the bias copy, indexed by its ordinal on the full barrier. -/
theorem ld_bias_group_column {p L m X g k} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g = 14)
    (won : ∀ i pc mask inst ld, X.get (g,i) = some ⟨pc,.elect mask inst ld⟩ → ld=laneOf L g)
    {pc al j org} {st q : Fin 2} {u : Nat}
    (issue : X.get (g,k) = some ⟨pc,.tensorIssue al (inputSpec p L (g/L.block) j org
      (obj L g (320+8*st.val)))⟩)
    (hoff : (Loader.inputSite j).sharedOffset=166912+32768*st.val+16384*q.val)
    (ord : ((X.tr g).take k).countP (issuesTo (obj L g (320+8*st.val))) = 2*u+q.val) :
    ∃ b < p.batch, tilePrefix p b*p.heads ≤ g/L.block ∧ g/L.block < tilePrefix p (b+1)*p.heads ∧
      let t := (Epilogue.assignedCoordinates p b (g/L.block)).1
      org 0 = Loader.biasOriginCol (decide (Loader.stageZeroBlocks p b t<Loader.tileBlocks p b t))
        st q u := by
  have hg := Frame.lt_of_get hX issue
  have hub : ∀ f, (⟨pc,.tensorIssue al (inputSpec p L (g/L.block) j org
      (obj L g (320+8*st.val)))⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨b,tt,c,v,kk,n,hs,h0,href⟩ := LdWarp.issue_state hp hX hf (.inl hw) issue
  let d : Loader.D := ⟨.tc tt c,v,kk⟩
  obtain ⟨ts,ins,o,hat,_,hc,fire⟩ :=
    Frame.fired_siteU (fun _ hg => thread_sound hp hg) hX issue hs hub
  have blk : d.site.blk=true := LdWarp.tc_blk tt c
  obtain ⟨R,bal,picked,_,su,_⟩ := LdWarp.tile_inv hp hX hg (.inl hw) k
    (List.getElem?_eq_some_iff.mp issue).1.le b d n hs h0 blk
  obtain ⟨req,num⟩ := Loader.tile_num hp hg picked
  obtain ⟨_,_,_,round,_⟩ := Loader.lfits_blk_of blk (href.2 h0).2
  have bias := Loader.bias_num hp hX hg hw hs h0
  have alt := Loader.tc_alt (o := 320+8*st.val) (by fin_cases st <;> simp)
    hp hX hg won (.inl hw) hs h0
  obtain ⟨xc,xr,xh,mb,rc,_,_,spec⟩ := Loader.tc_spec hp hg hat hc fire
  simp only [Kind.tensorIssue.injEq,inputSpec,TensorCopy.Spec.mk.injEq,TensorBox.mk.injEq] at spec
  obtain ⟨_,⟨_,_,origin,base,_⟩,_⟩ := spec
  have haddr := congrArg Loc.addr base
  simp only at haddr
  have tab : ∀ (tt : Fin 7) (c st q : Fin 2), (Loader.inputSite (Loader.siteOf tt c)).sharedOffset =
      166912+32768*st.val+16384*q.val → Loader.taOff tt=320+8*st.val ∧ c=q := by decide
  obtain ⟨off,rfl⟩ := tab tt c st q (by omega)
  rw [Loader.bias_col_reg tt c hat] at rc
  obtain rfl := (Value.bits.inj (Option.some.inj rc)).2
  refine ⟨req,num.batch,num.lo,num.hi,?_⟩
  rw [eq_of_heq origin]
  let t := (Epilogue.assignedCoordinates p req (g/L.block)).1
  let short := decide (Loader.stageZeroBlocks p req t < Loader.tileBlocks p req t)
  have gap : v.su.r29 = if short then Flow.Arith32.i32 (-1) else Flow.Arith32.i32 0 := by
    rw [show v.su = _ from su]
    simpa only [short,t,decide_eq_true_eq] using (Loader.bias_gap hp num).2
  have cnt : ((X.tr g).take k).countP (issuesTo (obj L g (320+8*st.val))) + (2-c.val) =
      2*n (.load (.acquire (obj L g (320+8*st.val+16)))) := by
    simp only [Loader.TcAlt,Loader.tcRem,off,ite_true] at alt
    exact alt
  have polls : LdWarp.lcn n (Loader.nE L g (decide (st=1))) = u+1 := by
    have num' : n (.load (.acquire (obj L g (320+8*st.val+16)))) = u+1 := by
      have := c.isLt
      omega
    fin_cases st <;> exact num'
  exact Loader.bias_col_of_count tt st c short off gap polls bias round

end PTX.Kernels.TmlFa4Fwd.Proof
