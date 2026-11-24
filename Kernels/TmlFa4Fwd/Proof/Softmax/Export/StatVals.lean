-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatValsState
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Statistics
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataFiring

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat} {a : Acc}
  {bs : List Byte}

/-- The bias and plain rounds' shared factor word at the S-full credit of the write. -/
theorem factor_write_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    (pl : Bool) (he : X.get (g,i) = some ⟨(Site.stat pl).pc,.wr a bs⟩)
    (hbefore : LoadsBefore L X (g,i)) :
    ∃ u w, Tm.sPolls L X g (Prologue.warpIndex L g / 4) i = u+1 ∧
      bs = w.toBytes ∧ Data.FactorWord w ((softRow p L X g).f u) := by
  obtain ⟨⟨s,v,k,acc⟩,n,c,rb,rp,hs,pcEq,hQ,_,hword,hpoll⟩ := stat_state hp hX hf hw hb he hbefore
  have eq : s = .stat pl := stat_site_of_pc (by cases pl <;> simp) pcEq
  subst s
  have hc := factor_ordinal hQ (pl := pl) rfl
  obtain ⟨_,_,hat,hfi⟩ := SmWarp.data_firing hp hX he hs
  obtain ⟨w,hbs,-,hr⟩ := Data.factor_word p L g v k acc pl hat hfi rfl
  refine ⟨c .sst+1,w,by omega,hbs,?_⟩
  simpa only [softRow, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hword] using hr

/-- The bias and plain rounds' shared factor word reads as the row's factor. -/
theorem factor_write_of_bias (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    (pl : Bool) (he : X.get (g,i) = some ⟨(Site.stat pl).pc,.wr a bs⟩)
    (hbefore : LoadsBefore L X (g,i)) :
    ∃ u w, Tm.sPolls L X g (Prologue.warpIndex L g / 4) i = u+1 ∧
      bs = w.toBytes ∧ Data.Reads w ((softRow p L X g).f u) :=
  let ⟨u, w, h1, h2, h3⟩ := factor_write_word hp hX hf hw hb pl he hbefore
  ⟨u, w, h1, h2, h3.reads⟩

/-- Both final shared words, including the encoded minus infinity of a fully masked row. -/
theorem final_write_of_bias (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    (j : Fin 2) (he : X.get (g,i) = some ⟨(Site.fin j).pc,.wr a bs⟩)
    (hbefore : LoadsBefore L X (g,i)) :
    bs = (if j = 0 then Value.float .f32 (softRow p L X g).rs
      else if softMaxFinite p L X g then Value.float .f32 (softRow p L X g).rm
      else ninf32).toBytes := by
  obtain ⟨⟨s,v,k,acc⟩,n,c,rb,rp,hs,pcEq,hQ,hF,hword,_⟩ := stat_state hp hX hf hw hb he hbefore
  have eq : s = .fin j := stat_site_of_pc (by fin_cases j <;> simp) pcEq
  subst s
  obtain ⟨hc,hpos⟩ := final_ordinal hQ hF (j := j) rfl
  obtain ⟨_,_,hat,hfi⟩ := SmWarp.data_firing hp hX he hs
  have h := Data.final_bytes p L g v k acc j hat hfi rfl
  match j with
  | 0 =>
    have e : c .sst = softRounds p L g - 1 := hc
    rw [e] at hword
    simpa only [softRow, ite_true, hword, Option.map_some, Option.getD_some] using h
  | 1 =>
    have e : c .sst = softRounds p L g := by change c .sst = _ - 1 + 1 at hc; omega
    rw [e] at hword
    cases hm : v.mf <;>
      simpa [softRow, softMaxFinite, hword, mxVal, hm] using h

end PTX.Kernels.TmlFa4Fwd.Proof.Values
