-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Async.AsyncExecution
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Tmem.TmemPairSize
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Proving `Correct`

* `size_le_count`, `size_le`: a bound on the counted events of every thread's trace bounds the
  size of every consistent execution.
* `terminates_of_count`: a uniform bound on the counted events of each thread gives a uniform
  bound on the size of every consistent execution.
* `Correct.exits`: every fair run of a correct kernel reaches completion.
-/

namespace PTX

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

private theorem sum_map_le_const {α : Type} (xs : List α) (f : α → Nat) (n : Nat)
    (h : ∀ x ∈ xs, f x ≤ n) : (xs.map f).sum ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    omega

private theorem counted_stages (xs : List Event) (f : Nat → Nat) (bound : Nat)
    (h : ∀ i (hi : i < xs.length), f i ≤ if (xs[i]).counts then bound else 0) :
    xs.countP Event.counts + ((List.range xs.length).map f).sum ≤
      (bound + 1) * xs.countP Event.counts := by
  induction xs generalizing f with
  | nil => simp
  | cons e es ih =>
    have h0 := h 0 (by simp)
    have ht := ih (fun i => f (i + 1)) (fun i hi => by
      exact h (i + 1) (by simpa using hi))
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.sum_cons, List.countP_cons, Function.comp_def, Nat.succ_eq_add_one]
    cases hc : e.counts <;> simp [hc] at h0 ⊢ <;>
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one] at ht ⊢ <;> omega

private theorem threadSize_le_count (X : Execution) (n : Nat) (hc : Consistent L K A mem0 X)
    (hc' : ∀ i s, X.Copy i s → s.dst.size ≤ 2 ^ 32)
    (h : ∀ g < L.threads, (X.tr g).countP Event.counts ≤ n) :
    X.threadSize L ≤ L.threads * ((asyncStageBound + 1 + 2 * L.grid) * n) := by
  apply (sum_map_le_const (List.range L.threads) _ ((asyncStageBound + 1 + 2 * L.grid) * n)
    ?_).trans_eq
    (by simp)
  intro g hg
  have ht := counted_stages (X.tr g) (fun i => X.asyncSize (g, i))
    (asyncStageBound + 2 * L.grid) (by
    intro i hi
    cases he : ((X.tr g)[i]).counts with
    | true => simp only [↓reduceIte]; exact X.asyncSize_le _ hc (fun s hs => hc' _ s hs)
    | false =>
      have hget : X.get (g, i) = some (X.tr g)[i] := List.getElem?_eq_getElem hi
      cases hev : (X.tr g)[i] with
      | mk pc kind =>
        cases kind <;> simp only [Event.counts, hev, Bool.true_eq_false] at he
        case wait m parity ok acquire scope =>
          cases ok <;> simp only [Bool.true_eq_false] at he
          rw [hev] at hget
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact Nat.le_of_eq (hc.failed_poll_no_effects hget))
  have hn := h g (List.mem_range.mp hg)
  have he : asyncStageBound + 2 * L.grid + 1 = asyncStageBound + 1 + 2 * L.grid := by omega
  rw [he] at ht
  exact ht.trans (Nat.mul_le_mul_left _ hn)

private theorem pairSize_le_count (X : Execution) (n : Nat) (hc : Consistent L K A mem0 X)
    (h : ∀ g < L.threads, (X.tr g).countP Event.counts ≤ n) :
    X.pairSize L ≤ L.grid * (L.threads * n) + L.threads * n := by
  have hb := sum_map_le_const (List.range L.grid) (fun cta => (X.tmemHistory cta).length)
    (L.threads * n)
    (fun cta _ => Tmem.Pair.RequestHistory.length_le (hc.tmemPair.1 cta).1
      (hc.object.tmemOrdered hc.tmemPair cta) n h)
  have hq := Tmem.Pair.pairing_length_le hc.tmemPair n h
  rw [List.length_range] at hb
  simp only [Execution.pairSize]
  omega

theorem size_le_count (X : Execution) (n : Nat) (hc : Consistent L K A mem0 X)
    (hc' : ∀ i s, X.Copy i s → s.dst.size ≤ 2 ^ 32)
    (h : ∀ g < L.threads, (X.tr g).countP Event.counts ≤ n) :
    X.size L ≤ L.threads * ((asyncStageBound + 1 + 2 * L.grid) * n) +
    (L.grid * (L.threads * n) + L.threads * n) :=
  Nat.add_le_add (threadSize_le_count X n hc hc' h) (pairSize_le_count X n hc h)

theorem size_le (X : Execution) (n : Nat) (hc : Consistent L K A mem0 X)
    (hc' : ∀ i s, X.Copy i s → s.dst.size ≤ 2 ^ 32)
    (h : ∀ g < L.threads, (X.tr g).length ≤ n) :
    X.size L ≤ L.threads * ((asyncStageBound + 1 + 2 * L.grid) * n) +
    (L.grid * (L.threads * n) + L.threads * n) :=
  size_le_count X n hc hc' (fun g hg => List.countP_le_length.trans (h g hg))

/-- Each counted instruction has a finite grid-dependent bound on asynchronous stages.
Failed polls cause none, so their unbounded repetition does not invalidate the bound. -/
theorem terminates_of_count (n : Nat)
    (h : ∀ X, Consistent L K A mem0 X → ∀ g < L.threads, (X.tr g).countP Event.counts ≤ n)
    (hc' : ∀ X, Consistent L K A mem0 X → ∀ i s, X.Copy i s → s.dst.size ≤ 2 ^ 32) :
    ∃ N, ∀ X, Consistent L K A mem0 X → X.size L ≤ N :=
  ⟨L.threads * ((asyncStageBound + 1 + 2 * L.grid) * n) +
    (L.grid * (L.threads * n) + L.threads * n),
    fun X hX => size_le_count X n hX (hc' X hX) (h X hX)⟩

/-- Every fair run of a correct kernel reaches completion, including CLC accounting and drainage. -/
theorem Correct.exits {post : FinalMem → Prop} (hc : Correct K A L mem0 post)
    (hv : L.Valid K) {Xs : Nat → Execution} (hr : FairRun L K A mem0 Xs) :
    ∃ n, Complete L (Xs n) := by
  by_contra hno
  push Not at hno
  obtain ⟨N, hN⟩ := hc.terminates hv
  have grow : ∀ i, ∃ n, i ≤ (Xs n).size L := by
    intro i
    induction i with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ i ih =>
      obtain ⟨n, hn⟩ := ih
      have hnm : ¬ Maximal L K A mem0 (Xs n) := fun hm => hno n (hc.progress hv _ hm)
      have hext : ∃ Y, Consistent L K A mem0 Y ∧ (Xs n).le Y ∧ (Xs n).size L < Y.size L := by
        by_contra h
        push Not at h
        exact hnm ⟨hr.1 n, fun Y hY hle => h Y hY hle⟩
      obtain ⟨k, hk⟩ := hr.2.2 n hext
      exact ⟨k, by omega⟩
  obtain ⟨n, hn⟩ := grow (N + 1)
  have := hN (Xs n) (hr.1 n)
  omega

end

end PTX
