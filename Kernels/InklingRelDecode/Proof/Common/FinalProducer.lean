-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.PreElect
public import Kernels.InklingRelDecode.Proof.Mma.Facts.Final
import Kernels.InklingRelDecode.Proof.Mma.Commit
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

def beforeFinalWorker {Q L g w x} : (workerCode Q L g w x).D → Prop
  | .inl d => dispatchBefore d
  | .inr ⟨.mma _,s⟩ => s.site.beforeFinal
  | .inr ⟨.loader _,_⟩ => False

def beforeFinalIssue {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),s⟩,_) => beforeFinalWorker s
  | _ => True

private theorem entered {Q L g} (s : Startup.D) (n : Cls → Nat) :
    beforeFinalIssue (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨site,t,x,w⟩ := s
  cases site <;> try trivial
  rename_i r
  cases r <;> first | trivial | exact ⟨rfl,.inl rfl⟩

private theorem dispatch_step {Q L m X g k w x d n e dn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X) (warp : g%L.block/32=7)
    (he : X.get (g,k)=some e) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl d⟩,n))) (early : dispatchBefore d)
    (step : Dispatch.next L g d e=some (some dn)) :
    beforeFinalWorker (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry dn) := by
  obtain ⟨s,r⟩ := d
  obtain ⟨rfl,h|h|h⟩ := early
  · cases h; cases step; exact ⟨rfl,.inr (.inl rfl)⟩
  · cases h; cases step; exact ⟨rfl,.inr (.inr rfl)⟩
  · cases h
    simp only [Dispatch.next] at step
    split at step <;> try contradiction
    rename_i a bs kind
    have bytes := dispatch_bytes hp hX words he hs rfl kind
    rw [warp] at bytes
    rw [show Dispatch.readTarget bs=some .mmaEntry from bytes ▸ Dispatch.role_target (3 : Fin 4)
      true] at step
    cases step; rfl

theorem before_final_issue {Q L m X g j st} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (wins : ElectLead L g (X.tr g))
    (missing : ∀ i sp, X.get (g,i)≠some ⟨2553,.tc (.commit sp)⟩)
    (bound : j≤(X.tr g).length) (hs : stateAt (thread Q L) X g j=some (some st))
    (nu : NoUbBefore X g j) : beforeFinalIssue st := by
  apply reference_induction beforeFinalIssue _ _ bound hs (prefix_ub_zero hs nu)
  · apply entered
  · rintro k ⟨s,c⟩ ev ⟨sn,cn⟩ he prev hu old move
    obtain ⟨sub,_⟩ := Code.counted_next_some move
    rcases s with s|⟨r,s⟩
    · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub
      apply entered
    · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some sub
      rcases r with (r|r)
      · cases r with
        | prologue => trivial
        | dispatch w x =>
          rcases s with s|⟨i,s⟩
          · change (Dispatch.next L g s ev).map _ = _ at step
            obtain ⟨_,go,h⟩ := Option.map_eq_some_iff.mp step
            obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
            exact dispatch_step hp hX words warp he prev old go
          · cases i with
            | loader => exact False.elim old
            | mma r =>
              change (Mma.next L g s ev).map _ = _ at step
              obtain ⟨_,go,h⟩ := Option.map_eq_some_iff.mp step
              obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
              have nf : s.site≠.finCommit := by
                obtain ⟨site,i,v⟩ := s
                rintro rfl
                have pc := event_pcU (fun g hg => thread_sound hp hg) hX he prev hu
                obtain ⟨_,_,_,hat,_,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg)
                  hX he prev hu
                have kind := Mma.commit_shape (regs := dispatchRegs Q L g w x) (w := w)
                  (i := i) (v := v) hp (lt_of_get hX he) .final hat hc fire
                have eq : ev=⟨2553,.tc (.commit (Mma.CommitSite.final.spec L g i))⟩ := by
                  cases ev; congr 1
                exact missing k _ (eq ▸ he)
              have live := Mma.stays_before go old nf (wins ev (List.mem_of_getElem? he))
              have stay : sn.site≠.dispatch := fun eq => by rw [eq] at live; cases live
              simp only [Code.backEnter,workerBack,stay,↓reduceIte]
              exact live
      · trivial

end PTX.Kernels.InklingRelDecode.Proof
