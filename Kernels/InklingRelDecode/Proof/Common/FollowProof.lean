-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataRef
public import Kernels.InklingRelDecode.Proof.Common.WorkerRef
import Kernels.InklingRelDecode.Proof.Common.DataInvNext
import Kernels.InklingRelDecode.Proof.Common.WorkerInvNext
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Startup.InvNext
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

private theorem start_enter_inv {Q L g n} (d : Startup.D) (hi : Startup.Inv L g d) :
    (thread Q L g).inv (Code.enter (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc) (Code.gatedExit Startup.enterOf (sel L g))
      d,n) := by
  obtain ⟨site,tm,x,w⟩ := d
  cases site <;> try exact ⟨hi,rfl⟩
  rename_i r
  cases r with
  | dp => exact ⟨⟨⟨rfl,rfl,rfl⟩,⟨fun _ => rfl,fun _ => ⟨_,rfl⟩⟩⟩,rfl⟩
  | worker => exact ⟨nofun,rfl⟩

private theorem structural {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads) (bound : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some s)) (zero : s.2 .ub=0) : (thread Q L g).inv s := by
  apply reference_induction (thread Q L g).inv _ _ bound hs zero
  · exact (thread_sound hp hg).start.choose_spec.2.2
  · rintro j ⟨s,n⟩ ev ⟨sn,nn⟩ get prev _ old move
    obtain ⟨step,_⟩ := Code.counted_next_some move
    rcases s with d|⟨r,s⟩
    · obtain ⟨_,sub,rfl⟩ := Code.glue_inl_some step
      exact start_enter_inv _ (Startup.inv_next old.1 sub)
    · obtain ⟨_,sub,rfl⟩ := Code.glue_inr_some step
      rcases r with (r|r)
      · cases r with
        | dispatch => exact worker_inv_next old sub
        | prologue => exact data_inv_next hp hX get prev old sub
      · cases sub

/-- All control and reference facts at every prefix, including the last state
when a silent segment may subsequently fault. -/
theorem follow_reads {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (pair : CountBytes Q L X) : Follow Q L X := by
  intro g hg k
  refine ⟨control_tracked hp hX g k hg,?_⟩
  intro s hs zero
  let j := min k (X.tr g).length
  have short : stateAt (thread Q L) X g j=some (some s) := by
    simpa only [j,stateAt,←List.take_eq_take_min] using hs
  have bound : j≤(X.tr g).length := Nat.min_le_right ..
  refine ⟨structural hp hX hg bound short zero,?_⟩
  obtain ⟨s,n⟩ := s
  rcases s with startup|⟨role,s⟩
  · trivial
  · rcases role with (role|stub)
    · cases role with
      | dispatch => exact worker_reference hp hX words pair bound short zero
      | prologue =>
        have ref := data_reference hp hX bound short zero
        rcases s with d|⟨ent,s⟩
        · exact ⟨data_warp hp hX bound short,ref.1⟩
        · rcases s with d|⟨_,d⟩
          · exact ref.1
          · exact ref
    · trivial

end PTX.Kernels.InklingRelDecode.Proof
