-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Common.EpilogueEvent
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
import Lemmas.Kernel.Safety.TableU

@[expose] public section

/-! # An epilogue lane past its first site has made the final poll

The epilogue's first site is the poll of `o_final` (pc 2565); the machine leaves it only by a
successful poll. So an event of a later site follows a successful poll of the lane. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem poll_step {ent L g d ev dn} (site : d.site = Epilogue.Site.wait)
    (step : Epilogue.Control.next ent L g d ev = some (some dn))
    (off : dn.site ≠ Epilogue.Site.wait) :
    ∃ l q ac sc, ev.kind = .wait l q true ac sc := by
  obtain ⟨s,r⟩ := d
  change s = Epilogue.Site.wait at site
  subst site
  obtain ⟨p,kd⟩ := ev
  cases kd with
  | wait l q ok ac sc =>
    simp only [Epilogue.Control.next] at step
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte] at step
      cases step
      exact absurd rfl off
    · exact ⟨l,q,ac,sc,rfl⟩
  | _ =>
    simp only [Epilogue.Control.next] at step
    cases step

private theorem epilogue_poll (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k w ent n} {d : Epilogue.Control.D} (hk : k ≤ (X.tr g).length)
    (nu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k = some (some (epiState w ent d n)))
    (off : d.site ≠ Epilogue.Site.wait) :
    ∃ u l q ac sc, u < k ∧ X.get (g,u) = some ⟨2565,.wait l q true ac sc⟩ := by
  induction k using Nat.strong_induction_on generalizing d n with
  | _ k ih =>
    have later : d ≠ ({} : Epilogue.Control.D) := fun h => off (by rw [h])
    obtain ⟨u,old,cnt,ev,eq,hs',get,mv⟩ := epi_prev hk later hs
    have clean : ∀ f, ev.kind ≠ .ub f := nu u (by omega) ev get
    by_cases w2 : old.site = Epilogue.Site.wait
    · obtain ⟨l,q,ac,sc,kind⟩ := poll_step w2 mv off
      have pc := event_pcU (fun g h => thread_sound hp h) hX get hs' clean
      change ev.pc = old.site.pc at pc
      obtain ⟨p,kd⟩ := ev
      change kd = _ at kind
      subst kind
      have p2565 : p = 2565 := (show p = old.site.pc from pc).trans (by rw [w2]; rfl)
      subst p2565
      exact ⟨u,l,q,ac,sc,by omega,get⟩
    · obtain ⟨u',l,q,ac,sc,lt,got⟩ := ih u (by omega) (by omega)
        (fun j hj => nu j (by omega)) hs' w2
      exact ⟨u',l,q,ac,sc,by omega,got⟩

/-- **An epilogue event after the poll site follows a successful poll of `o_final`.** -/
public theorem epilogue_event_poll {g k pc kd} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,kd⟩) (nu : ∀ f, kd ≠ .ub f) (lo : 2566 ≤ pc) (hi : pc < 2853) :
    ∃ u l q ac sc, u < k ∧ X.get (g,u) = some ⟨2565,.wait l q true ac sc⟩ := by
  obtain ⟨w,ent,d,n,t,ins,u2,hs,-,-,pcd,-⟩ := epilogue_event_entry hp hX hf he nu
    (by show 2565 ≤ pc; omega) hi
  refine epilogue_poll hp hX (List.getElem?_eq_some_iff.mp he).1.le (noUbBefore_of_get hX he) hs
    (fun hw => ?_)
  change pc = d.site.pc at pcd
  rw [hw] at pcd
  exact absurd pcd (by change pc ≠ 2565; omega)

end PTX.Kernels.InklingRelDecode.Proof.Export
