-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.FollowStartup
public import Kernels.InklingRelDecode.Proof.Common.FollowStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

private def active {Q L g} : (thread Q L g).D → Prop
  | (.inl _,_) => True
  | (.inr ⟨.inl (.dispatch ..),d⟩,_) => WorkerActive d
  | (.inr ⟨.inl (.prologue _),d⟩,_) => DataActive d
  | (.inr ⟨.inr _,_⟩,_) => False

private theorem enter_active {Q L g} (s : Startup.D) (n : Cls → Nat) : active
    (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> try trivial
  rename_i r
  cases r
  · exact nofun
  · exact ⟨nofun,nofun⟩

private theorem active_step {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {s : (thread Q L g).D} {e}
    (he : X.get (g,k) = some e) (hs : Frame.stateAt (thread Q L) X g k = some (some s))
    (h : active s) : AdvancesIn active ((thread Q L g).next s e) := by
  obtain ⟨s,n⟩ := s
  rcases s with s | ⟨r,d⟩
  · rw [next_start]
    exact advances_map (startup_no_stop hp hX he hs) (fun _ => enter_active ..)
  rcases r with r | r
  · cases r with
    | dispatch w x =>
      have next := worker_advances d e h
      change AdvancesIn active ((((workerCode Q L g w x).next d e).map
        (Option.map (fun t => Sum.inr ⟨.inl (.dispatch w x),t⟩))).map
          (Option.map fun t => (t,Code.bump cls n e)))
      rcases hn : (workerCode Q L g w x).next d e with _ | _ | t <;> rw [hn] at next <;> exact next
    | prologue w =>
      have next := data_advances d e h
      change AdvancesIn active ((((dataCode Q L g w).next d e).map
        (Option.map (fun t => Sum.inr ⟨.inl (.prologue w),t⟩))).map
          (Option.map fun t => (t,Code.bump cls n e)))
      rcases hn : (dataCode Q L g w).next d e with _ | _ | t <;> rw [hn] at next <;> exact next
  · exact h.elim

/-- The control machine follows all seven fragments, for every value of the shared
words. Establish this before interpreting any load across threads. -/
theorem control_tracked {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    Frame.Tracked (thread Q L) X := by
  apply Frame.tracked_of_followed (J := fun _ => active) (Frame.inductive_lex (fun _ => 0))
  · intro g _
    exact enter_active ..
  · intro g k d e he hs act _
    have good := active_step hp hX he hs act
    unfold Frame.StepGood
    rcases hn : (thread Q L g).next d e with _ | _ | t <;> rw [hn] at good
    · exact ⟨nofun,fun _ => nofun⟩
    · exact good.elim
    · exact ⟨nofun,fun d eq => by cases eq; exact good⟩

end
end PTX.Kernels.InklingRelDecode.Proof
