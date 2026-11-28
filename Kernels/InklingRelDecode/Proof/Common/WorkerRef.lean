-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerRefGlue
public import Kernels.InklingRelDecode.Proof.Common.ReferenceInduction
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Frame PTX.Flow

private def workerLocal {Q L g} : (thread Q L g).D → Prop
  | (.inl _,n) => noWorkerPolls n
  | (.inr ⟨.inl (.dispatch w x),s⟩,n) => workerInv Q L g w x s n
  | _ => True

private theorem entered_ref {Q L g n} (old : noWorkerPolls n) (s : Startup.D) :
    workerLocal (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> try exact old
  rename_i r
  cases r with
  | dp => trivial
  | worker => exact ⟨Dispatch.allowed_init,Dispatch.busy_init _,fun _ => old,fun h => absurd rfl h⟩

theorem worker_reference {Q L m X g k w x d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (bytes : CountBytes Q L X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.dispatch w x),d⟩,n)))
    (zero : n .ub=0) : workerInv Q L g w x d n := by
  have old : workerLocal (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.dispatch w x),d⟩,n) := by
    apply reference_induction workerLocal _ _ hk hs zero
    · apply entered_ref
      exact ⟨rfl,rfl,rfl,rfl⟩
    · rintro j ⟨s,c⟩ ev ⟨sn,cn⟩ get prev hu ih move
      obtain ⟨sub,count⟩ := Code.counted_next_some move
      change cn=Code.bump cls c ev at count
      subst cn
      rcases s with s|⟨r,s⟩
      · have pc := event_pcU (fun g hg => thread_sound hp hg) hX get prev hu
        change ev.pc=s.site.pc at pc
        have quiet (s : Startup.Site) : s.pc≠2374 ∧ s.pc≠2462 ∧ s.pc≠2510 ∧ s.pc≠2550 ∧
            s.pc≠2551 := by
          cases s <;> first | decide | (rename_i r; cases r <;> decide)
        obtain ⟨a,b,c,e,f⟩ := quiet s.site
        obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub
        exact entered_ref (bump_no_polls ih (pc ▸ a) (pc ▸ b) (pc ▸ c) (pc ▸ e) (pc ▸ f)) _
      · obtain ⟨_,fired,rfl⟩ := Code.glue_inr_some sub
        rcases r with (r|r)
        · cases r with
          | dispatch => exact ref_worker_next hp hX words bytes get hu prev ih fired
          | prologue => trivial
        · trivial
  cases d <;> trivial

end PTX.Kernels.InklingRelDecode.Proof
