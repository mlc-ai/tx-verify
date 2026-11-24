-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasReturnLeader
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Loader
open PTX.Kernels.TmlFa4Fwd.Softmax

private theorem count_disjoint {xs : List Event} (p q : Event → Bool)
    (hNone : ∀ e, p e = true → q e = false) :
    xs.countP (fun e => p e || q e) = xs.countP p + xs.countP q := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.countP_cons, ih]
    cases hp : p e
    · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.add_assoc]
    · have hq := hNone e hp
      simp [hq]
      omega

private def acquireMarker (n : Nat) (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => e.pc == n
  | _ => false

private theorem acquireMarkerShape {n : Nat} {e : Event} (h : acquireMarker n e = true) :
    ∃ target p a s, e = ⟨n, .wait target p true a s⟩ := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [acquireMarker] at h
  rename_i target phase ok acq scope
  cases ok
  · cases h
  · change (pc == n) = true at h
    obtain rfl := beq_iff_eq.mp h
    exact ⟨target, phase, acq, scope, rfl⟩

private theorem releaseReadBudget {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g j : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (biasEmptyObject l cta stage) 0 1 true .cta) :
    arrivals (biasEmptyObject l cta stage) ((X.tr g).take j) + 1 ≤
      okPolls (biasReadyObject l cta stage) ((X.tr g).take j) := by
  obtain ⟨k, he⟩ := hIssue
  have hs := actualBiasEmptyArrivalSite hp hX stage he rfl
  obtain ⟨_, _, _, _, _, hLoc⟩ := biasEmptyArriveFacts hp hX he hs
  have hCta : cta = g / l.block := congrArg Loc.cta hLoc
  have hA := congrArg Loc.addr hLoc
  change l.sharedBase + (336 + 8 * stage.val) =
    l.sharedBase + (336 + 8 * (Prologue.warpIndex l g / 4)) at hA
  have hStage : Prologue.warpIndex l g / 4 = stage.val := by omega
  let earlier := (X.tr g).take j
  let ret := fun b : Bool => fun e : Event => e.pc == if b then 5278 else 3590
  let ready := biasReadyObject l cta stage
  let retObj := biasEmptyObject l cta stage
  have hLower : arrivals retObj earlier ≤ earlier.countP (ret false) +
      earlier.countP (ret true) := by
    rw [← count_disjoint (ret false) (ret true) (by simp [ret]; omega)]
    apply List.countP_mono_left
    intro event hIn hP
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hIn)
    obtain ⟨pc, kind⟩ := event
    cases kind <;> simp [arrivesOn, sourceArrive] at hP
    rename_i target tx count rel scope
    subst target
    have h := actualBiasEmptyArrivalSite hp hX stage (i := (g,i)) hi rfl
    simpa [ret] using h
  have hUpper : earlier.countP (acquireMarker 3498) + earlier.countP (acquireMarker 5181) ≤
      okPolls ready earlier := by
    rw [← count_disjoint (acquireMarker 3498) (acquireMarker 5181) (by
      intro e he
      obtain ⟨_, _, _, _, rfl⟩ := acquireMarkerShape he
      rfl)]
    apply List.countP_mono_left
    intro event hIn hP
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hIn)
    have mark (n : Nat) (hn : n ∈ [3498, 5181]) (hM : acquireMarker n event = true) :
        okPoll ready event = true := by
      obtain ⟨target, phase, acq, scope, rfl⟩ := acquireMarkerShape hM
      have hTarget := biasReadyWaitAddress hp hX (g := g) (index := i) hi hn
      have hReady : target = ready := by
        unfold ready biasReadyObject
        rw [hTarget, hStage, hCta]
      simp [sourceWaitSuccess, hReady]
    simp only [Bool.or_eq_true] at hP
    rcases hP with h | h
    · exact mark 3498 (by decide) h
    · exact mark 5181 (by decide) h
  have hBudget := actualBiasReadBudget hp hX he hs
  change earlier.countP (ret false) + earlier.countP (ret true) + 1 ≤
    earlier.countP (acquireMarker 3498) + earlier.countP (acquireMarker 5181) at hBudget
  change arrivals retObj earlier + 1 ≤ okPolls ready earlier
  omega

/-- A Bias return resumes after the successful Bias-ready acquire of its own local
release ordinal. -/
theorem biasReadyAcquireOfReturn {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g j : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (biasEmptyObject l cta stage) 0 1 true .cta) :
    let ready := biasReadyObject l cta stage
    let ordinal := arrivals (biasEmptyObject l cta stage) ((X.tr g).take j)
    ∃ k e q acq sc, X.get (g,k) = some e ∧ e.kind = .wait ready q true acq sc ∧
      okPolls ready ((X.tr g).take k) = ordinal ∧ Resumes kernel X (g,k) (g,j) := by
  obtain ⟨k, source, phase, acq, sc, hk, he, hNth⟩ :=
    MbarRing.Poll.exists_nth (releaseReadBudget hp hX stage hIssue)
  obtain ⟨out, hCanonical⟩ := actualCanonicalPoll hX he
  obtain ⟨_, hGet⟩ := hIssue
  have hTrace : TraceBefore X (g,k) (g,j) := ⟨rfl, hk, (List.getElem?_eq_some_iff.mp hGet).1⟩
  refine ⟨k, _, phase, acq, sc, he, rfl, hNth, hTrace, ?_⟩
  simp only [he, Option.map_some, Kind.resume]
  exact ⟨source, out, _, phase, acq, sc, he, hCanonical, hTrace⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Softmax
