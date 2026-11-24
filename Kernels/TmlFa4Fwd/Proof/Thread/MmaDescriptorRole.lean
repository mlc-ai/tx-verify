-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorProjection
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- The surrounding MMA control is common to key and value descriptors.
Only these two windows and the final path need operand-specific proofs. -/
structure DescriptorWindows (l : Launch) (g : Nat) (select : Event → Bool)
    (observes : Nat → Event → Prop) where
  quiet : ∀ e, e.pc < 2287 ∨ (2529 ≤ e.pc ∧ e.pc < 2534) → select e = false
  polls : ∀ (i : Fin 4) e, e.pc = (waitSite (descriptorReadyWait i)).pc → select e = false
  value : ∀ {use s es vs}, use % 2 = 1 → At s 2297 (ringFrame l 7207 7208 use) →
    Walk kernel Assumptions.all l g s es vs →
    (∀ {u tail post}, At u 2344 (ringFrame l 7207 7208 use) →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      DescriptorTrace select observes (use + 1) tail) →
    DescriptorTrace select observes (use + 1) es
  key : ∀ {use s es vs}, use % 2 = 0 → At s 2355 (ringFrame l 1192 2572 use) →
    Walk kernel Assumptions.all l g s es vs →
    (∀ {u tail post}, At u 2524 (ringFrame l 1192 2572 use) →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      DescriptorTrace select observes (use + 1) tail) →
    DescriptorTrace select observes (use + 1) es
  tail : ∀ {use s es vs}, use % 2 = 1 → At s 2534 (ringFrame l 7207 7208 use) →
    Walk kernel Assumptions.all l g s es vs → DescriptorTrace select observes use es
  skip : ∀ {s es vs}, At s 2763 (readyFrame l) →
    Walk kernel Assumptions.all l g s es vs → DescriptorTrace select observes 0 es

variable {p : Params} {l : Launch} {m : Mem0} {g : Nat} {select : Event → Bool}
variable {observes : Nat → Event → Prop}

variable (hp : Pre p l m) (hRole : DescriptorWindows l g select observes)
include hp hRole

private theorem steadyDescriptorTrace {use : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (hOdd : use % 2 = 1) (ht : At t 2291 (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g t es vs) :
    DescriptorTrace select observes use es := by
  generalize hLength : vs.length = fuel
  induction fuel using Nat.strong_induction_on generalizing use t es vs with
  | h fuel ih =>
    apply descriptorTraceLocal (select := select) (observes := observes)
      (readyAddress hp g 0 use) ht hw
    intro u v huv hLen hWalk
    apply descriptorTracePoll (select := select) (observes := observes) hp 1
      (by simp [descriptorReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
      (by simp [descriptorReadyWait, waitSite, readyAddressSite])
      (by simp [descriptorReadyWait, waitSite, readyAddressSite, ringFrame])
      (fun _ => hRole.polls 1 _ rfl) huv hWalk
    intro a ee avs hALen ha hA
    have hAtV : At a 2297 (ringFrame l 7207 7208 use) :=
      ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.2⟩
    apply hRole.value hOdd hAtV hA
    intro b be bvs hb hBLen hB
    apply descriptorTraceLocal (select := select) (observes := observes)
      (readyAdvanceFramed l g 0 use) hb hB
    intro c cvs hc hCLen hC
    apply descriptorTraceLocal (select := select) (observes := observes)
      (readyAddress hp g 1 (use + 1)) hc hC
    intro d dvs hd hDLen hD
    apply descriptorTracePoll (select := select) (observes := observes) hp 2
      (by simp [descriptorReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
      (by simp [descriptorReadyWait, waitSite, readyAddressSite])
      (by simp [descriptorReadyWait, waitSite, readyAddressSite, ringFrame])
      (fun _ => hRole.polls 2 _ rfl) hd hD
    intro e ee evs hELen he hE
    have hAtK : At e 2355 (ringFrame l 1192 2572 (use + 1)) :=
      ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.2⟩
    apply hRole.key (by omega) hAtK hE
    intro f fe fvs hf hFLen hF
    apply descriptorTraceLocal (select := select) (observes := observes)
      (readyAdvanceFramed l g 1 (use + 1)) hf hF
    intro j jvs hj hJLen hJ
    apply descriptorTraceInterval (select := select) (observes := observes) 6 (by rw [hj.1]; decide)
      (fun event h => hRole.quiet event (.inr h)) ⟨rfl, hj.2⟩
      (by simp [ringFrame, readyFrame, readyAdvanceSite])
      (by simp [ringFrame, readyFrame, readyAdvanceSite, readyInterval]) hJ
    intro k ke kvs hExit hk hKLen hK
    have hPc : k.pc = 2291 ∨ k.pc = 2534 := by simpa [readyInterval] using hExit
    rcases hPc with hSteady | hTail
    · exact ih kvs.length (by omega) (by omega) ⟨hSteady, hk.2⟩ hK rfl
    · exact hRole.tail (by omega) ⟨hTail, hk.2⟩ hK

private theorem descriptorsAfterFirst {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 2148 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs) :
    DescriptorTrace select observes 1 es := by
  apply descriptorTraceInterval (select := select) (observes := observes) 2 (by rw [ht.1]; decide)
    (fun e h => hRole.quiet e (.inl (show e.pc < 2287 from (show e.pc < 2280 from h.2).trans
      (by decide)))) ⟨rfl, ht.2⟩
    (by simp [readyFrame]) (by simp [readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hw'
  have hu' : At u 2280 (readyFrame l) := ⟨by simpa [readyInterval] using hExit, hu.2⟩
  apply descriptorTraceLocal (select := select) (observes := observes) (readySeedShort l g) hu' hw'
  intro v visits hv _ hw''
  apply descriptorTraceInterval (select := select) (observes := observes) 3 (by rw [hv.1]; decide)
    (fun e h => hRole.quiet e (.inl h.2)) ⟨rfl, hv.2⟩
    (by simp [ringFrame, readyFrame]) (by simp [ringFrame, readyFrame, readyInterval]) hw''
  intro w rest wVisits hExit hwAt _ hWalk
  have hPc : w.pc = 2287 ∨ w.pc = 2534 := by simpa [readyInterval] using hExit
  rcases hPc with hSteady | hTail
  · have hSeed : At w 2287 (readyFrame l) :=
      ⟨hSteady, hwAt.2.1, hwAt.2.2.1, hwAt.2.2.2.1, hwAt.2.2.2.2.2.2⟩
    apply descriptorTraceLocal (select := select) (observes := observes)
      (readySeedSteady l g) hSeed hWalk
    intro z post hz _ hW
    exact steadyDescriptorTrace hp hRole (by decide) hz hW
  · exact hRole.tail (by decide) ⟨hTail, hwAt.2⟩ hWalk

/-- Replay startup, the steady loop, and the final path for a descriptor observation. -/
theorem descriptorTraceFromEntry {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs) :
    DescriptorTrace select observes 0 es := by
  apply descriptorTraceInterval (select := select) (observes := observes) 0 (by rw [ht.1]; decide)
    (fun e h => hRole.quiet e (.inl ((show e.pc < 2140 from h.2).trans (by decide))))
    ⟨rfl, ht.2⟩ (by simp [readyFrame]) (by simp [readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hw'
  have hPc : u.pc = 2140 ∨ u.pc = 2763 := by simpa [readyInterval] using hExit
  rcases hPc with hInit | hSkip
  · apply descriptorTraceLocal (select := select) (observes := observes)
      (readyInitialPhase l g) ⟨hInit, hu.2⟩ hw'
    intro v visits hv _ hw''
    apply descriptorTraceInterval (select := select) (observes := observes) 1 (by rw [hv.1]; decide)
      (fun e h => hRole.quiet e (.inl ((show e.pc < 2144 from h.2).trans (by decide))))
      ⟨rfl, hv.2⟩ (by simp [readyFrame]) (by simp [readyFrame, readyInterval]) hw''
    intro w rest wVisits hExit hwAt _ hw'''
    have hwAt' : At w 2144 ((2536, b32 0) :: readyFrame l) :=
      ⟨by simpa [readyInterval] using hExit, hwAt.2⟩
    apply descriptorTraceLocal (select := select) (observes := observes)
      (readyInitialAddress hp g) hwAt' hw'''
    intro z zVisits hz _ hzWalk
    apply descriptorTracePoll (select := select) (observes := observes) hp 0
      (by simp [descriptorReadyWait, waitSite, readyFrame])
      (by simp [descriptorReadyWait, waitSite, readyAddr, readyStage, MbarRing.Index.slot])
      (by simp [descriptorReadyWait, waitSite, readyWord, MbarRing.Index.round])
      (fun _ => hRole.polls 0 _ rfl) hz hzWalk
    intro f suffix fVisits _ hf hWalk
    have hf' : At f 2148 (readyFrame l) :=
      ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.2⟩
    exact descriptorsAfterFirst hp hRole hf' hWalk
  · exact hRole.skip ⟨hSkip, hu.2⟩ hw'

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
