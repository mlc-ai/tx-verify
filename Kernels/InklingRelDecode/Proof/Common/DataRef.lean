-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataRefStep
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Frame PTX.Flow

private def dataLocal {Q L g} : (thread Q L g).D → Prop
  | (.inl s,n) => LaunchCounts n (Startup.barriers s.site)
  | (.inr ⟨.inl (.prologue _),s⟩,n) => dataRef s n
  | _ => True

private theorem entered_data {Q L g n} (s : Startup.D)
    (h : LaunchCounts n (Startup.barriers s.site)) :
    dataLocal (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> try exact h
  rename_i r
  cases r with
  | worker => trivial
  | dp =>
    change LaunchCounts n 2 at h
    refine ⟨pro_history_start h,?_,h.poll _ (by decide)⟩
    simp [softCounts,h.poll _ (by decide : 27≤1257),h.poll _ (by decide : 27≤2239),
      h.visit _ (by decide : 27≤1013)]

theorem data_reference {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.prologue w),d⟩,n)))
    (zero : n .ub=0) : dataRef d n := by
  apply reference_induction dataLocal _ _ hk hs zero
  · exact entered_data _ launch_counts_init
  · rintro j ⟨s,c⟩ ev ⟨sn,cn⟩ get prev hu ih move
    obtain ⟨sub,count⟩ := Code.counted_next_some move
    change cn=Code.bump cls c ev at count
    subst cn
    rcases s with s|⟨r,s⟩
    · obtain ⟨_,step,rfl⟩ := Code.glue_inl_some sub
      exact entered_data _ (launch_counts_step ih (start_ev hp hX get prev hu) step)
    · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some sub
      rcases r with (r|r)
      · cases r with
        | prologue => exact data_ref_next hp hX get hu prev ih step
        | dispatch => trivial
      · trivial

/-- The history of the prologue site a step is taken from. -/
theorem data_ref_get {Q L m X g j ev w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,j)=some ev)
    (prev : stateAt (thread Q L) X g j=some (some (.inr ⟨.inl (.prologue w),d⟩,n))) :
    dataRef d n :=
  data_reference hp hX (List.getElem?_eq_some_iff.mp get).1.le prev
    (prefix_ub_zero prev (Frame.noUbBefore_of_get hX get))

end PTX.Kernels.InklingRelDecode.Proof
