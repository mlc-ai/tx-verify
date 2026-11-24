-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundVisit
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatValsIndex
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax
variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat} {d : D} {e : Event}

theorem soft_round_counts (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) (he : X.get (g,i) = some e)
    (hs : softState p L X g i = some d) :
    ∃ c rb rp ns nv, RefQ p L g (Control.erase d).scheduler c rb rp ∧
      SmWarp.SFits p L g (Control.erase d).scheduler ns nv ∧
      Tm.sPolls L X g (Prologue.warpIndex L g/4) i = c (.acquire 80) ∧
      ((X.tr g).take i).countP (Softmax.cls L g .sst) = c .sst := by
  unfold softState at hs
  split at hs
  · rename_i v n hd
    cases Option.some.inj hs
    have ctrl := control_of_data hp hd
    obtain ⟨⟨c,⟨⟨rb,rp,hQ⟩⟩,link⟩,fit⟩ :=
      ((SmWarp.good hp hX hw (Frame.lt_of_get hX he) rfl i).2 _ ctrl).2 (ub_zero hX he ctrl)
    exact ⟨_,_,_,_,_,hQ,fit,((tm_counts hw ctrl).1).trans (link _ rfl).symm,
      (count_at hw ctrl (c := .sst) rfl).trans (link _ rfl).symm⟩
  · cases hs

private theorem common (z : Bool) :
    (ptsOf z (.acquire 80)).countP inBias = 1 ∧ (ptsOf z (.acquire 80)).countP inPlain = 1 ∧
      (ptsOf z .sst).countP inBias = 1 ∧ (ptsOf z .sst).countP inPlain = 1 := by
  cases z <;> decide +kernel

theorem first_at_pack (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) (he : X.get (g,i) = some e)
    {r q v k acc u} (hs : softState p L X g i = some ⟨.pst r q,v,k,acc⟩)
    (hu : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1) : u = 0 ↔ r = .first := by
  obtain ⟨c,rb,rp,_,_,ref,_,poll,_⟩ := soft_round_counts hp hX hw he hs
  obtain ⟨b,f,_⟩ := common (lz L g)
  have cnt := ref.cnt (.acquire 80) rfl
  change c (.acquire 80) = passed _ (.pst r q) rb rp at cnt
  have vals : ∀ (lz : Bool) (r : Rd) (q : Fin 4),
      (ptsOf lz (.acquire 80)).countP (Softmax.before (.pst r q)) =
        (if r = .first then 1 else 2) := by intro z r; cases r <;> revert z <;> decide +kernel
  simp only [passed,vals,b,f,Nat.mul_one] at cnt
  by_cases h : r = .first
  · subst r
    have pre : ∀ q : Fin 4, preR (.pst .first q) = true := by decide +kernel
    obtain ⟨a,b⟩ := ref.pre (pre q)
    simp only [ite_true] at cnt
    exact iff_of_true (by omega) rfl
  · simp only [h,ite_false] at cnt
    exact iff_of_false (by omega) h

theorem soft_final_credit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) (he : X.get (g,i) = some e)
    {v k acc} (hs : softState p L X g i = some ⟨.fin 0,v,k,acc⟩) :
    Tm.sPolls L X g (Prologue.warpIndex L g/4) i = softRounds p L g := by
  obtain ⟨c,rb,rp,_,_,ref,fit,poll,_⟩ := soft_round_counts hp hX hw he hs
  obtain ⟨h,pos⟩ := final_ordinal ref fit (j := 0) rfl
  change c .sst = softRounds p L g - 1 + 0 at h
  have sc := ref.cnt (.acquire 80) rfl
  have st := ref.cnt .sst rfl
  change c (.acquire 80) = passed _ (.fin 0) rb rp at sc
  change c .sst = passed _ (.fin 0) rb rp at st
  have pre : ∀ z : Bool, (ptsOf z (.acquire 80)).countP (Softmax.before (.fin 0)) = 1 ∧
      (ptsOf z .sst).countP (Softmax.before (.fin 0)) = 0 := by decide +kernel
  obtain ⟨a,b⟩ := pre (lz L g)
  obtain ⟨u,v,w,x⟩ := common (lz L g)
  simp only [passed,a,b,u,v,w,x,Nat.mul_one] at sc st
  omega

/-- The phase before the first score poll has zero credit. -/
theorem wq_credit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) (he : X.get (g,i) = some e)
    (hs : softState p L X g i = some d) (site : d.site = .wq) :
    Tm.sPolls L X g (Prologue.warpIndex L g/4) i = 0 := by
  obtain ⟨c,rb,rp,_,_,ref,_,poll,_⟩ := soft_round_counts hp hX hw he hs
  have place : (Control.erase d).scheduler.site = .wq := site
  obtain ⟨b,f⟩ := ref.pre (by rw [place]; rfl)
  have eq := ref.cnt (.acquire 80) rfl
  rw [place,b,f] at eq
  have tab : ∀ z : Bool, (ptsOf z (.acquire 80)).countP (Softmax.before .wq) = 0 := by
    decide +kernel
  simpa only [passed,Nat.zero_mul,Nat.add_zero,tab] using poll.trans eq

end PTX.Kernels.TmlFa4Fwd.Proof.Values
