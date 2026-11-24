-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Lib.Start
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX.Flow

theorem tc_blk (t : Fin 7) (q : Fin 2) : (Loader.Site.tc t q).blk = true := by
  fin_cases t <;> rfl

/-- The loader site and reference counts at a tensor issue. -/
theorem issue_state {p L m X g i pc a spec} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g=14 ∨ Prologue.warpIndex L g=15)
    (he : X.get (g,i) = some ⟨pc,.tensorIssue a spec⟩) :
    ∃ (b : Bool) (tt : Fin 7) (q : Fin 2) (v : Loader.V) (k : Fin 2) (n : Cls → Nat),
      let d : Loader.D := ⟨.tc tt q,v,k⟩
      Frame.stateAt (thread p L) X g i = some (some (linj p L g b d n)) ∧ n .ub=0 ∧
      Ref p L (Prologue.warpIndex L g) g (linj p L g b d n) := by
  have hub : ∀ f, (⟨pc,.tensorIssue a spec⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  rcases open_ev hp hX hf hw he hub with ⟨_,_,_,_,_,hi,ev⟩ | ⟨b,⟨s,v,k⟩,n,hs,h0,ref,_,ev⟩
  · exact (start_no_tensor ev hi.2).elim
  obtain ⟨_,_,site,_⟩ := Loader.copy_site ev hub
  obtain ⟨tt,q,h⟩ := site.mp ⟨_,_,rfl⟩
  change s = _ at h
  subst s
  exact ⟨b,tt,q,v,k,n,hs,h0,ref⟩

end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
