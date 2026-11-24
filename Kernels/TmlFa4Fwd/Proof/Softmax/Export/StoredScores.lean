-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.ReadRegion
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundCredit
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Lemmas.Kernel.FrameU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The score-read hypothesis of the protocol link for one lane. -/
abbrev ScoreReads (L : Launch) (X : Execution) (g : Nat) (S : Nat → Nat → ℝ) :=
  ∀ {i a j u : Nat} {vs : List Value}, X.TLd (g,i) a vs .s32x32b → j < vs.length →
    Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1 →
    vs[j]? = some (.float .f32 (S u
      ((tcDataCell32 L g a j).column - 128*(Prologue.warpIndex L g/4))))

private theorem score_chunk {i r c v k acc e d'} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hw : Prologue.warpIndex L g < 8)
    (he : X.get (g,i) = some e) (hs : softState p L X g i = some ⟨.sld r c,v,k,acc⟩)
    (hn : succ p L g ⟨.sld r c,v,k,acc⟩ e = some (some d'))
    {S : Nat → Nat → ℝ} (reads : ScoreReads L X g S) {u}
    (credit : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1) (j : Fin 32) :
    d'.v.score (32*c.val+j.val) = S u (32*c.val+j.val) := by
  have ev := softState_event hp hX he hs
  rcases ev.1 with ⟨a,vs,sh,kind⟩ | ⟨f,h⟩
  · obtain ⟨pc,kd⟩ := e
    change kd = _ at kind
    subst kd
    unfold softState at hs
    split at hs
    · rename_i d n hd
      cases Option.some.inj hs
      have ctl := control_of_data hp hd
      obtain ⟨ts,ins,o,hat,_,code,fire⟩ := Frame.fired_siteU (fun _ hg => thread_sound hp hg)
        hX he ctl (by intro _ h; cases h)
      obtain ⟨rfl,column,len⟩ := sld_col (r := r) (c := c)
        (v := (Control.erase ⟨.sld r c,v,k,acc⟩).v.scheduler) (k := k) (acc := acc)
        hat code fire rfl
      rw [colS_eq hw] at column
      have sc (j : Nat) (hj : j < vs.length) :
          vs[j] = .float .f32 (S u (32*c.val+j)) := by
        have inCol : (tcDataCell32 L g a j).column - 128*(Prologue.warpIndex L g/4) =
            32*c.val+j := by
          change a%65536+j-128*(g%L.block/32/4) = _
          omega
        simpa only [List.getElem?_eq_getElem hj,Option.some.injEq,inCol] using
          reads (a := a) ⟨pc,he⟩ hj credit
      have f32 : F32s vs := by
        intro w h
        obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem h
        exact ⟨_,sc j hj⟩
      obtain ⟨d,step,record⟩ := Data.score_load p L g r c v k acc
        ⟨pc,.tc (.ld a vs .s32x32b)⟩ (a := a) (sh := .s32x32b) rfl f32
      have eq := Option.some.inj (Option.some.inj (step.symm.trans hn))
      subst d'
      have hj : j.val < vs.length := by rw [len]; exact j.isLt
      have val := (record j.val j.isLt hj).symm.trans (sc j.val hj)
      exact (Value.float.inj val).2
    · cases hs
  · exact (ev.2 f h).elim

/-- At a P store all 128 score registers contain this round's score reads. -/
theorem soft_stored_scores (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) {S : Nat → Nat → ℝ} (reads : ScoreReads L X g S)
    {i r q v k acc u} (hs : softState p L X g i = some ⟨.pst r q,v,k,acc⟩)
    (hi : i ≤ (X.tr g).length) (credit : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1)
    (col : Fin 128) : v.score col.val = S u col.val := by
  let c : Fin 4 := ⟨col.val/32,by have := col.isLt; omega⟩
  let j : Fin 32 := ⟨col.val%32,Nat.mod_lt _ (by decide)⟩
  have splitCol : 32*c.val+j.val = col.val := by dsimp [c,j]; omega
  obtain ⟨cut,store,frame⟩ := score_region r c (lz L g)
  let Q (i : Nat) (d : D) := Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1 →
    d.v.score col.val = S u col.val
  apply soft_region_induct hp _ _ cut Q (i := i) (d := ⟨.pst r q,v,k,acc⟩) _ hi hs (store q) credit
  intro i d d' e he prev hn _ ih
  rcases ih with ⟨inside,prior⟩ | src
  · obtain ⟨body,off,other⟩ := frame _ inside
    have keep := Data.score_frame hn body c other
    have hc : (⟨col.val/32%4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = c := by
      apply Fin.ext; exact Nat.mod_eq_of_lt c.isLt
    intro h
    have eq := prior ((soft_credit_step hw he (softState_event hp hX he prev) off).symm.trans h)
    simpa only [V.score,hc,keep] using eq
  · have site := beq_iff_eq.mp src
    obtain ⟨s,v',k',acc'⟩ := d
    change s = .sld r c at site
    subst s
    intro h
    have hc := (soft_credit_step hw he (softState_event hp hX he prev)
      (by change (0 : Nat) ≠ 80; decide)).symm.trans h
    simpa only [splitCol] using score_chunk hp hX hw he prev hn reads hc j

end PTX.Kernels.TmlFa4Fwd.Proof.Values
