-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Prologue
public import Lemmas.Flow.Shuffle

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section

variable {A : List Assumption}

private theorem broadcastRunInv {l : Launch} {g pc dst : Nat} {t s : TState} {src : Value}
    {e : Event} {rest : List Event} {o : Option TState} (hp : s.pc = pc)
    (hn : Next kernel A l g t s (broadcastTemplate s dst src))
    (hr : Run kernel A l g t (e :: rest) o) :
    ∃ recv ok, e = ⟨pc, .shfl .idx src 0 31 recv ok⟩ ∧
      Run kernel A l g (next (setReg s dst recv)) rest o ∧
      EStep kernel A l g s e (some (next (setReg s dst recv))) := by
  have hs : Stops kernel A l g s := ⟨_, hn.stop⟩
  cases hr with
  | step hlocal he hrest =>
    have heq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst s
    obtain ⟨templ, htempl, hfire⟩ := he
    rw [hn.stop] at htempl
    obtain rfl := Out.ev.inj htempl
    rw [hp] at hfire
    obtain ⟨recv, ok, hev, hstate⟩ := broadcastFires hfire
    cases hstate
    exact ⟨recv, ok, hev, hrest, ⟨_, hn.stop, by rw [hp]; exact hfire⟩⟩
  | last hlocal he =>
    have heq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst s
    obtain ⟨templ, htempl, hfire⟩ := he
    rw [hn.stop] at htempl
    obtain rfl := Out.ev.inj htempl
    obtain ⟨_, _, _, hstate⟩ := hfire
    cases hstate

private theorem firstShape [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads) (e : Event)
    (he : X.get (g, 0) = some e) :
    ∃ recv ok, e = ⟨25, .shfl .idx (b32 l.sharedBase) 0 31 recv ok⟩ := by
  obtain ⟨s, hs, hAt⟩ := firstBroadcastWith (A := A) hpre g
  obtain ⟨o, hrun⟩ := hX.thr g hg
  cases htr : X.tr g with
  | nil => simp [Execution.get, htr] at he
  | cons hd rest =>
    have he' : hd = e := by simpa [Execution.get, htr] using he
    rw [htr, he'] at hrun
    obtain ⟨recv, ok, hshape, _⟩ := broadcastRunInv hAt.1 hs hrun
    exact ⟨recv, ok, hshape⟩

/-- In a consistent execution, the first broadcast actually returns the dynamic shared base
from the lane-zero peer. -/
theorem firstSharedValue [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads) {e : Event}
    (he : X.get (g, 0) = some e) :
    e = ⟨25, .shfl .idx (b32 l.sharedBase) 0 31 (b32 l.sharedBase) true⟩ := by
  obtain ⟨recv, ok, rfl⟩ := firstShape hpre hX g hg e he
  have hpos : 0 < l.block := by rw [hpre.block]; decide
  obtain ⟨rfl, rfl⟩ := PTX.Flow.first_shfl_value hX hpos
    (v := fun _ => b32 l.sharedBase) (firstShape hpre hX) (fun _ _ _ => rfl) hg he
  rfl

private theorem prefixCount {α : Type} {is : α → Bool} : ∀ {xs : List α} {n : Nat},
    n ≤ xs.length → (∀ j < n, ∀ e, xs[j]? = some e → is e = true) →
    (xs.take n).countP is = n
  | _, 0, _, _ => rfl
  | [], n + 1, h, _ => by simp at h
  | a :: xs, n + 1, h, hall => by
    have ha : is a = true := hall 0 (by omega) a rfl
    have hlen : n ≤ xs.length := by simpa using Nat.le_of_succ_le_succ h
    have hh : ∀ j < n, ∀ e, xs[j]? = some e → is e = true := by
      intro j hj e he
      exact hall (j + 1) (by omega) e he
    simp [List.take_succ_cons, ha, prefixCount hlen hh]

private theorem prefixShflReturn {l : Launch} {m : Mem0} {X : Execution} {n : Nat}
    {v : Nat → Nat → Value} (hX : Consistent l kernel A m X) (hpos : 0 < l.block)
    (hshape : ∀ g < l.threads, ∀ j ≤ n, ∀ ev, X.get (g, j) = some ev →
      ∃ pc recv ok, ev = ⟨pc, .shfl .idx (v j g) 0 31 recv ok⟩)
    (hunif : ∀ g h, SameWarp l g h → v n h = v n g) {g pc : Nat} (hg : g < l.threads) {recv : Value}
    {ok : Bool} (he : X.get (g, n) = some ⟨pc, .shfl .idx (v n g) 0 31 recv ok⟩) :
    recv = v n g ∧ ok = true := by
  have count (g' : Nat) (hg' : g' < l.threads) (k : Nat) (hkn : k ≤ n + 1)
      (hk : k ≤ (X.tr g').length) : ((X.tr g').take k).countP Execution.isShfl = k := by
    refine prefixCount hk (fun j hj ev hev => ?_)
    obtain ⟨_, _, _, rfl⟩ := hshape g' hg' j (by omega) ev hev
    rfl
  have ith (g' : Nat) {j : Nat} {ev : Event} (he' : X.get (g', j) = some ev) :
      j < (X.tr g').length := (List.getElem?_eq_some_iff.mp he').choose
  have hcount := count g hg n (by omega) (Nat.le_of_lt (ith g he))
  have hk : X.ShflK (g, n) n := ⟨⟨_, _, _, _, _, _, _, he⟩, hcount⟩
  refine PTX.Flow.nth_shfl_value hX hpos (v := v n) ?_ hunif ?_ hg he hk
  · intro g' hg' i pc' mode a b c r o hi he'
    have hlen := ith g' he'
    have hni : n ≤ i := by
      have hb := List.countP_le_length (p := Execution.isShfl) (l := (X.tr g').take i)
      change ((X.tr g').take i).countP Execution.isShfl ≤ _ at hb
      have hc := hi.2
      change ((X.tr g').take i).countP Execution.isShfl = n at hc
      rw [List.length_take, hc] at hb
      omega
    have hnlen : n < (X.tr g').length := by omega
    have hnget : X.get (g', n) = some (X.tr g')[n] := List.getElem?_eq_getElem hnlen
    obtain ⟨pc'', ret, ok', hshape'⟩ := hshape g' hg' n (by omega) _ hnget
    have hget' : X.get (g', n) = some ⟨pc'', .shfl .idx (v n g') 0 31 ret ok'⟩ := by
      rw [hnget, hshape']
    have hk' : X.ShflK (g', n) n :=
      ⟨⟨_, _, _, _, _, _, _, hget'⟩, count g' hg' n (by omega) (by omega)⟩
    obtain rfl := shfl_index_unique hi hk'
    rw [hget'] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.shfl.injEq] at he'
    exact he'.2.2.1.symm
  · rintro g' hg' ⟨k, pc', hx, hc⟩
    by_cases hkn : k ≤ n
    · obtain ⟨_, _, _, he'⟩ := hshape g' hg' k hkn _ hx
      cases he'
    · have hk' : n + 1 ≤ (X.tr g').length := by have := ith g' hx; omega
      have hd := count g' hg' (n + 1) (by omega) hk'
      have hle : ((X.tr g').take (n + 1)).countP Execution.isShfl ≤
          ((X.tr g').take k).countP Execution.isShfl :=
        (List.take_prefix_take_left (l := X.tr g') (i := n + 1) (j := k)
          (by omega)).sublist.countP_le
      omega

private theorem abiDisjoint (p : Params) (l : Launch) :
    List.Disjoint ((abiFacts p l).map Prod.fst)
      [2535, 1061, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1062] := by
  change List.Disjoint [1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498, 7499, 7500,
    7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294, 7295, 1665]
    [2535, 1061, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1062]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem abiAfterSet {p : Params} {l : Launch} {t : TState} {r : Nat} {v : Value}
    (hfacts : Holds t.regs (abiFacts p l))
    (hr : r ∈ [2535, 1061, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1062]) :
    Holds (next (setReg t r v)).regs (abiFacts p l) := by
  apply holds_update hfacts
  intro x hx heq
  apply abiDisjoint p l (List.mem_map_of_mem (f := Prod.fst) hx)
  exact heq.symm ▸ hr

private theorem holdsFrame {R R' : Nat → Option Value} {fs : List (Nat × Value)}
    (h : Holds R fs) (hf : ∀ x ∈ fs, R' x.1 = R x.1) : Holds R' fs := by
  induction fs with
  | nil => trivial
  | cons a rest ih =>
    obtain ⟨r, v⟩ := a
    exact ⟨(hf (r, v) (by simp)).trans h.1, ih h.2 (fun x hx => hf x (by simp [hx]))⟩

private theorem firstTail [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads) {f : Event}
    {es : List Event} (htr : X.tr g = f :: es) :
    ∃ t o, t.pc = 26 ∧ t.fault = none ∧
      t.regs 2535 = some (b32 l.sharedBase) ∧ Holds t.regs (abiFacts p l) ∧
      t.sub = 0 ∧ t.acc = [] ∧ Run kernel A l g t es o ∧
      Run kernel A l g {} [f] (some t) := by
  have he : X.get (g, 0) = some f := by simp [Execution.get, htr]
  have hval := firstSharedValue hpre hX g hg he
  obtain ⟨s, hn, hAt⟩ := firstBroadcastWith (A := A) hpre g
  obtain ⟨o, hrun⟩ := hX.thr g hg
  rw [htr] at hrun
  obtain ⟨recv, ok, h, hrest, hStep⟩ := broadcastRunInv hAt.1 hn hrun
  rw [hval] at h
  cases h
  refine ⟨next (setReg s 2535 (b32 l.sharedBase)), o, ?_, hAt.2.2.2.1, rfl,
    abiAfterSet hAt.2.2.2.2 (by decide), hAt.2.1, hAt.2.2.1, hrest,
    .step hn.steps hStep (.nil _)⟩
  change s.pc + 1 = 26
  rw [hAt.1]

private theorem secondTail [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads) {f e : Event}
    {es : List Event} (htr : X.tr g = f :: e :: es) :
    ∃ s o recv ok, e = ⟨34, .shfl .idx (b32 (warpIndex l g)) 0 31 recv ok⟩ ∧
      s.pc = 34 ∧ s.fault = none ∧ s.regs 2535 = some (b32 l.sharedBase) ∧
      s.regs 1061 = some (b32 (g % l.block)) ∧
      Holds s.regs (abiFacts p l) ∧ s.sub = 0 ∧ s.acc = [] ∧
      Run kernel A l g (next (setReg s 1673 recv)) es o ∧
      Run kernel A l g {} [f, e] (some (next (setReg s 1673 recv))) := by
  obtain ⟨t, o, hp, hf, hb, habi, hSub, hAcc, hr, hPrefix⟩ := firstTail hpre hX g hg htr
  obtain ⟨u, hrun, hpc, hfu, hwu, hTid, hs, ha, hframe⟩ :=
    warpIndexLocalWithTid (A := A) hpre g t hp hf
  have hNext : Next kernel A l g t u (broadcastTemplate u 1673 (b32 (warpIndex l g))) :=
    ⟨run_rtg hrun, startupOut (.inl (by rw [hpc]; decide))
      (warpBroadcastOut (stage := 0) hpre.block hpc hfu hwu)⟩
  obtain ⟨recv, ok, hEq, hTail, hStep⟩ := broadcastRunInv hpc hNext hr
  refine ⟨u, o, recv, ok, hEq, hpc, hfu, (hframe 2535 (by decide)).trans hb, hTid,
    holdsFrame habi (fun x hx => hframe x.1 ?_), hs.trans hSub, ha.trans hAcc, hTail,
    hPrefix.snoc hNext.steps hStep⟩
  intro hm
  have h₁ := List.mem_map_of_mem (f := Prod.fst) hx
  exact abiDisjoint p l h₁ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto)

private theorem secondShape [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat)
    (hg : g < l.threads) {e : Event} (he : X.get (g, 1) = some e) :
    ∃ recv ok, e = ⟨34, .shfl .idx (b32 (warpIndex l g)) 0 31 recv ok⟩ := by
  cases htr : X.tr g with
  | nil => simp [Execution.get, htr] at he
  | cons f es =>
    cases es with
    | nil => simp [Execution.get, htr] at he
    | cons e' rest =>
      have hi : e' = e := by simpa [Execution.get, htr] using he
      subst e'
      obtain ⟨_, _, recv, ok, hshape, _⟩ := secondTail hpre hX g hg htr
      exact ⟨recv, ok, hshape⟩

/-- The second shuffle returns the warp index from the matching lane-zero peer. -/
theorem secondWarpValue [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads) {e : Event}
    (he : X.get (g, 1) = some e) :
    e = ⟨34, .shfl .idx (b32 (warpIndex l g)) 0 31 (b32 (warpIndex l g)) true⟩ := by
  obtain ⟨recv, ok, rfl⟩ := secondShape hpre hX g hg he
  have hpos : 0 < l.block := by rw [hpre.block]; decide
  let v (j g' : Nat) := if j = 0 then b32 l.sharedBase else b32 (warpIndex l g')
  have shape (g' : Nat) (hg' : g' < l.threads) (j : Nat) (hj : j ≤ 1) (e : Event)
      (he' : X.get (g', j) = some e) :
      ∃ pc recv ok, e = ⟨pc, .shfl .idx (v j g') 0 31 recv ok⟩ := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos'
    · obtain ⟨recv, ok, hs⟩ := firstShape hpre hX g' hg' e he'
      exact ⟨25, recv, ok, hs⟩
    · obtain rfl : j = 1 := by omega
      obtain ⟨recv, ok, hs⟩ := secondShape hpre hX g' hg' he'
      exact ⟨34, recv, ok, hs⟩
  have unif (g' h : Nat) (h' : SameWarp l g' h) : v 1 h = v 1 g' :=
    congrArg b32 h'.2.symm
  obtain ⟨rfl, rfl⟩ := prefixShflReturn hX hpos shape unif hg he
  rfl

private theorem thirdTail [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    {f₀ f₁ e : Event} {es : List Event} (htr : X.tr g = f₀ :: f₁ :: e :: es) :
    ∃ s o recv ok, e = ⟨35, .shfl .idx (b32 (warpIndex l g)) 0 31 recv ok⟩ ∧
      s.pc = 35 ∧ s.fault = none ∧ s.regs 2535 = some (b32 l.sharedBase) ∧
      s.regs 1061 = some (b32 (g % l.block)) ∧
      Holds s.regs (abiFacts p l) ∧ s.sub = 0 ∧ s.acc = [] ∧
      Run kernel A l g (next (setReg s 1062 recv)) es o ∧
      Run kernel A l g {} [f₀, f₁, e] (some (next (setReg s 1062 recv))) := by
  have he : X.get (g, 1) = some f₁ := by simp [Execution.get, htr]
  have hval := secondWarpValue hpre hX g hg he
  obtain ⟨t, o, recv, ok, hf₁, hp, hf, hb, hTid, habi, hSub, hAcc, hr, hPrefix⟩ :=
    secondTail hpre hX g hg htr
  rw [hval] at hf₁
  cases hf₁
  let s := next (setReg t 1673 (b32 (warpIndex l g)))
  have hp' : s.pc = 35 := by change t.pc + 1 = 35; rw [hp]
  have hNext : Next kernel A l g s s (broadcastTemplate s 1062 (b32 (warpIndex l g))) :=
    ⟨.refl, startupOut (.inl (by rw [hp']; decide))
      (warpBroadcastOut (stage := 1) hpre.block hp' hf rfl)⟩
  obtain ⟨ret, ok', hshape, hTail, hStep⟩ := broadcastRunInv hp' hNext hr
  exact ⟨s, o, ret, ok', hshape, hp', hf, hb, hTid, abiAfterSet habi (by decide), hSub, hAcc,
    hTail, hPrefix.snoc hNext.steps hStep⟩

private theorem thirdShape [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads) {e : Event}
    (he : X.get (g, 2) = some e) :
    ∃ recv ok, e = ⟨35, .shfl .idx (b32 (warpIndex l g)) 0 31 recv ok⟩ := by
  cases htr : X.tr g with
  | nil => simp [Execution.get, htr] at he
  | cons f₀ es =>
    cases es with
    | nil => simp [Execution.get, htr] at he
    | cons f₁ es =>
      cases es with
      | nil => simp [Execution.get, htr] at he
      | cons e' rest =>
        have hi : e' = e := by simpa [Execution.get, htr] using he
        subst e'
        obtain ⟨_, _, recv, ok, hshape, _⟩ := thirdTail hpre hX g hg htr
        exact ⟨recv, ok, hshape⟩

/-- The third shuffle also returns the warp index from the lane-zero peer. -/
theorem thirdWarpValue [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads) {e : Event}
    (he : X.get (g, 2) = some e) :
    e = ⟨35, .shfl .idx (b32 (warpIndex l g)) 0 31 (b32 (warpIndex l g)) true⟩ := by
  obtain ⟨recv, ok, rfl⟩ := thirdShape hpre hX g hg he
  have hpos : 0 < l.block := by rw [hpre.block]; decide
  let v (j g' : Nat) := if j = 0 then b32 l.sharedBase else b32 (warpIndex l g')
  have shape (g' : Nat) (hg' : g' < l.threads) (j : Nat) (hj : j ≤ 2) (e : Event)
      (he' : X.get (g', j) = some e) :
      ∃ pc recv ok, e = ⟨pc, .shfl .idx (v j g') 0 31 recv ok⟩ := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos'
    · obtain ⟨recv, ok, hs⟩ := firstShape hpre hX g' hg' e he'
      exact ⟨25, recv, ok, hs⟩
    · by_cases h : j = 1
      · subst j
        obtain ⟨recv, ok, hs⟩ := secondShape hpre hX g' hg' he'
        exact ⟨34, recv, ok, hs⟩
      · obtain rfl : j = 2 := by omega
        obtain ⟨recv, ok, hs⟩ := thirdShape hpre hX g' hg' he'
        exact ⟨35, recv, ok, hs⟩
  have unif (g' h : Nat) (h' : SameWarp l g' h) : v 2 h = v 2 g' :=
    congrArg b32 h'.2.symm
  obtain ⟨rfl, rfl⟩ := prefixShflReturn hX hpos shape unif hg he
  rfl

/-- Any trace that completes the three prologue broadcasts continues with its warp index and
shared base in the expected registers at the role split. -/
theorem broadcastPrefixRun [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    {f₀ f₁ f₂ : Event} {es : List Event} (htr : X.tr g = f₀ :: f₁ :: f₂ :: es) :
    ∃ t o, t.pc = 36 ∧ t.fault = none ∧ t.regs 2535 = some (b32 l.sharedBase) ∧
      t.regs 1062 = some (b32 (warpIndex l g)) ∧ t.regs 1061 = some (b32 (g % l.block)) ∧
      Holds t.regs (abiFacts p l) ∧
      t.sub = 0 ∧ t.acc = [] ∧ Run kernel A l g t es o ∧
      Run kernel A l g {} [f₀, f₁, f₂] (some t) := by
  have he : X.get (g, 2) = some f₂ := by simp [Execution.get, htr]
  have hval := thirdWarpValue hpre hX g hg he
  obtain ⟨s, o, recv, ok, hf₂, hp, hf, hb, hTid, habi, hSub, hAcc, hr, hPrefix⟩ :=
    thirdTail hpre hX g hg htr
  rw [hval] at hf₂
  cases hf₂
  refine ⟨next (setReg s 1062 (b32 (warpIndex l g))), o, ?_, hf, hb, rfl, hTid,
    abiAfterSet habi (by decide), hSub, hAcc, hr, hPrefix⟩
  change s.pc + 1 = 36
  rw [hp]

theorem broadcastPrefixWithTid [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat)
    (hg : g < l.threads) {f₀ f₁ f₂ : Event} {es : List Event} (htr : X.tr g = f₀ :: f₁ :: f₂ :: es)
    :
    ∃ t o, t.pc = 36 ∧ t.fault = none ∧ t.regs 2535 = some (b32 l.sharedBase) ∧
      t.regs 1062 = some (b32 (warpIndex l g)) ∧ t.regs 1061 = some (b32 (g % l.block)) ∧
      Holds t.regs (abiFacts p l) ∧
      t.sub = 0 ∧ t.acc = [] ∧ Run kernel A l g t es o := by
  obtain ⟨t, o, hPc, hFault, hBase, hWarp, hTid, hAbi, hSub, hAcc, hRun, _⟩ :=
    broadcastPrefixRun hpre hX g hg htr
  exact ⟨t, o, hPc, hFault, hBase, hWarp, hTid, hAbi, hSub, hAcc, hRun⟩

theorem broadcastPrefix [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    {f₀ f₁ f₂ : Event} {es : List Event} (htr : X.tr g = f₀ :: f₁ :: f₂ :: es) :
    ∃ t o, t.pc = 36 ∧ t.fault = none ∧ t.regs 2535 = some (b32 l.sharedBase) ∧
      t.regs 1062 = some (b32 (warpIndex l g)) ∧ Holds t.regs (abiFacts p l) ∧
      t.sub = 0 ∧ t.acc = [] ∧ Run kernel A l g t es o := by
  obtain ⟨t, o, hpc, hf, hBase, hWarp, _, hAbi, hSub, hAcc, hRun⟩ :=
    broadcastPrefixWithTid (A := A) hpre hX g hg htr
  exact ⟨t, o, hpc, hf, hBase, hWarp, hAbi, hSub, hAcc, hRun⟩

private theorem fixedTail {l : Launch} {g : Nat} {a b : TState} {e : Event} {es : List Event}
    {o : Option TState} {m : Tmpl} (hn : Next kernel A l g a b m)
    (hf : ∀ ret, Fires b.pc m e ret → ret = some (next b)) (hr : Run kernel A l g a (e :: es) o) :
    Fires b.pc m e (some (next b)) ∧ Run kernel A l g (next b) es o := by
  have hs : Stops kernel A l g b := ⟨_, hn.stop⟩
  cases hr with
  | step hlocal he hrest =>
    have heq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst b
    obtain ⟨templ, htempl, hfire⟩ := he
    rw [hn.stop] at htempl
    obtain rfl := Out.ev.inj htempl
    have hstate := hf _ hfire
    cases hstate
    exact ⟨hfire, hrest⟩
  | last hlocal he =>
    have heq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst b
    obtain ⟨templ, htempl, hfire⟩ := he
    rw [hn.stop] at htempl
    obtain rfl := Out.ev.inj htempl
    have hstate := hf _ hfire
    cases hstate

private theorem fenceOut {l : Launch} {g : Nat} {t : TState} (hp : t.pc = 172)
  (hf : t.fault = none) :
    out kernel [] l g t = .ev (.fenceMbarInit (next t)) := by
  unfold out
  rw [hp, hf, Flow.code_172]
  rfl

private theorem barOut {l : Launch} {g : Nat} {t : TState} (hp : t.pc = 173) (hf : t.fault = none) :
    out kernel [] l g t = .ev (.bar 0 (next t) none .sync) := by
  unfold out
  rw [hp, hf, Flow.code_173]
  rfl

private theorem setMaxRegOut {l : Launch} {g : Nat} {t : TState}
    (hp : t.pc = Flow.setMaxReg_2) (hf : t.fault = none) :
    out kernel [] l g t = .ev (.setMaxReg false 80 (next t)) := by
  unfold out
  rw [hp, hf, Flow.code_2769]
  rfl

/-- The first six events of each warp-13 lane leave it at the scheduler's first local
instruction with the exact ABI, barrier and scheduler operands. -/
theorem warp13Startup [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    (hw : warpIndex l g = 13) {e₀ e₁ e₂ e₃ e₄ e₅ : Event} {es : List Event}
    (htr : X.tr g = e₀ :: e₁ :: e₂ :: e₃ :: e₄ :: e₅ :: es) :
    e₃ = ⟨172, .fenceMbarInit⟩ ∧ e₄ = ⟨173, .bar 0 none .sync⟩ ∧
      (∃ inst, e₅ = ⟨2769, .setMaxReg false 80 inst⟩) ∧
      ∃ u o, Run kernel A l g u es o ∧ u.pc = 2770 ∧ u.fault = none ∧
        u.regs 2535 = some (b32 l.sharedBase) ∧ u.regs 1062 = some (b32 13) ∧
        u.regs 2390 = some (b32 (l.sharedBase + 208)) ∧
        u.regs 6497 = some (b32 (l.sharedBase + 224)) ∧
        u.regs 1072 = some (b32 (g / l.block)) ∧
        u.regs 1178 = some (b32 (l.sharedBase + 68608)) ∧ u.regs 7228 = some (b32 p.batch) ∧
        u.regs 7502 = some (b64 p.cuQBase) ∧ u.regs 7506 = some (b64 p.cuQBase) ∧
        u.regs 7290 = some (.ptr 64 false (.param (param 10)) 0) ∧ u.sub = 0 ∧ u.acc = [] := by
  obtain ⟨t, o, hpc, hf, hbase, hwarp, habi, hSub, hAcc, hrun⟩ := broadcastPrefix hpre hX g hg htr
  rw [hw] at hwarp
  obtain ⟨u, hr, hp, hfu, _, _, _, _, _, _, _, h208, _, _, h224, _, hSubU, hAccU, hframe⟩ :=
    nonzeroWarpWith (A := A) hpre g 13 t (by decide) (by decide) hpc hf hwarp hbase
  have hNext : Next kernel A l g t u (.fenceMbarInit (next u)) :=
    ⟨run_rtg hr, startupOut (.inl (by rw [hp]; decide)) (fenceOut hp hfu)⟩
  obtain ⟨hfence, hr'⟩ := fixedTail hNext (fun _ h => h.2) hrun
  let v := next u
  have hpv : v.pc = 173 := by change u.pc + 1 = 173; rw [hp]
  have hNext' : Next kernel A l g v v (.bar 0 (next v) none .sync) :=
    ⟨.refl, startupOut (.inl (by rw [hpv]; decide)) (barOut hpv hfu)⟩
  obtain ⟨hbar, hr''⟩ := fixedTail hNext' (fun _ h => h.2) hr'
  let w := next v
  have hpw : w.pc = 174 := by change v.pc + 1 = 174; rw [hpv]
  have hrw : w.regs = u.regs := rfl
  have hwarp' : w.regs 1062 = some (b32 13) :=
    (congrFun hrw 1062).trans ((hframe 1062 (by decide)).trans hwarp)
  have hbase' : w.regs 2535 = some (b32 l.sharedBase) :=
    (congrFun hrw 2535).trans ((hframe 2535 (by decide)).trans hbase)
  obtain ⟨z, hdispatch, hzp, hzf, hcta, hbuf, hbatch, hSubZ, hAccZ, hframe'⟩ :=
    warp13DispatchWith (A := A) hpre g w hg hpw hfu hwarp' hbase'
  have hSet : Next kernel A l g w z (.setMaxReg false 80 (next z)) :=
    ⟨run_rtg hdispatch, startupOut (.inr (.inr (by rw [show z.pc = 2769 from hzp]; decide)))
      (setMaxRegOut hzp hzf)⟩
  obtain ⟨hset, hrFinal⟩ := fixedTail hSet (fun _ h => h.choose_spec.2) hr''
  obtain ⟨inst, hi, _⟩ := hset
  have hzp' : z.pc = 2769 := hzp
  rw [hzp'] at hi
  have hfenceEvent : e₃ = ⟨172, .fenceMbarInit⟩ := hp ▸ hfence.1
  have hbarEvent : e₄ = ⟨173, .bar 0 none .sync⟩ := hpv ▸ hbar.1
  have hzReady : z.regs 2390 = some (b32 (l.sharedBase + 208)) :=
    (hframe' 2390 (by decide)).trans ((congrFun hrw 2390).trans h208)
  have hzFree : z.regs 6497 = some (b32 (l.sharedBase + 224)) :=
    (hframe' 6497 (by decide)).trans ((congrFun hrw 6497).trans h224)
  have keep (r : Nat) (h₁ : r ∉ [18, 19, 1063, 22, 1064, 1065, 27, 1066, 1067, 32, 1068,
      6495, 37, 42, 2390, 47, 1069, 1070, 52, 6497, 57, 1071])
      (h₂ : r ∉ [1072, 1706, 60, 1178, 263, 7228]) : z.regs r = t.regs r := by
    rw [hframe' r h₂, hrw, hframe r h₁]
  have hq : (7502, b64 p.cuQBase) ∈ abiFacts p l := by simp [abiFacts]
  have hq' : (7506, b64 p.cuQBase) ∈ abiFacts p l := by simp [abiFacts]
  have ho : (7290, .ptr 64 false (.param (param 10)) 0) ∈ abiFacts p l := by simp [abiFacts]
  exact ⟨hfenceEvent, hbarEvent, ⟨inst, hi⟩, next z, o, hrFinal,
    by change z.pc + 1 = 2770; rw [hzp], hzf,
    (hframe' 2535 (by decide)).trans hbase', (hframe' 1062 (by decide)).trans hwarp',
    hzReady, hzFree, hcta, hbuf, hbatch, (keep 7502 (by decide) (by decide)).trans
      (holds_mem habi hq),
    (keep 7506 (by decide) (by decide)).trans (holds_mem habi hq'),
    (keep 7290 (by decide) (by decide)).trans (holds_mem habi ho),
    hSubZ.trans (hSubU.trans hSub), hAccZ.trans (hAccU.trans hAcc)⟩

/-- The fourth and fifth events of each nonzero-warp lane are the barrier-init fence and the
common barrier, whatever the length of its trace. -/
theorem nonzeroFenceBar [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat)
    (hg : g < l.threads) (hw : 0 < warpIndex l g) {e₀ e₁ e₂ : Event} {es : List Event}
    (htr : X.tr g = e₀ :: e₁ :: e₂ :: es) :
    (∀ e, es[0]? = some e → e = ⟨172, .fenceMbarInit⟩) ∧
      (∀ e, es[1]? = some e → e = ⟨173, .bar 0 none .sync⟩) := by
  obtain ⟨t, o, hpc, hf, hbase, hwarp, -, -, -, hrun⟩ := broadcastPrefix hpre hX g hg htr
  obtain ⟨u, hr, hp, hfu, -⟩ := nonzeroWarpWith (A := A) hpre g (warpIndex l g) t hw
    (warpIndex_lt hpre g) hpc hf hwarp hbase
  have hNext : Next kernel A l g t u (.fenceMbarInit (next u)) :=
    ⟨run_rtg hr, startupOut (.inl (by rw [hp]; decide)) (fenceOut hp hfu)⟩
  match es, hrun with
  | [], _ => exact ⟨fun e h => by simp at h, fun e h => by simp at h⟩
  | e₃ :: rest, hrun =>
    obtain ⟨hfence, hr'⟩ := fixedTail hNext (fun _ h => h.2) hrun
    have h3 : e₃ = ⟨172, .fenceMbarInit⟩ := hp ▸ hfence.1
    refine ⟨fun e h => by simp at h; rw [← h, h3], fun e h => ?_⟩
    match rest, hr' with
    | [], _ => simp at h
    | e₄ :: rest', hr' =>
      have hpv : (next u).pc = 173 := by change u.pc + 1 = 173; rw [hp]
      have hNext' : Next kernel A l g (next u) (next u) (.bar 0 (next (next u)) none .sync) :=
        ⟨.refl, startupOut (.inl (by rw [hpv]; decide)) (barOut hpv hfu)⟩
      obtain ⟨hbar, -⟩ := fixedTail hNext' (fun _ h => h.2) hr'
      simp at h
      rw [← h]
      exact hpv ▸ hbar.1

/-- The first five events of each warp-13 lane (the three broadcasts, the barrier-init fence and
the common barrier) leave it at the common dispatch, whose local steps reach the warp's
`setmaxnreg` with the launch registers the output warp keeps. -/
theorem warp13StartupAt [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hpre : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    (hw : warpIndex l g = 13) {e₀ e₁ e₂ e₃ e₄ : Event} {es : List Event}
    (htr : X.tr g = e₀ :: e₁ :: e₂ :: e₃ :: e₄ :: es) :
    e₃ = ⟨172, .fenceMbarInit⟩ ∧ e₄ = ⟨173, .bar 0 none .sync⟩ ∧
      ∃ w z o, Run kernel A l g w es o ∧ Relation.ReflTransGen (Tau kernel A l g) w z ∧
        z.pc = 2769 ∧ z.fault = none ∧ z.sub = 0 ∧ z.acc = [] ∧
        z.regs 2535 = some (b32 l.sharedBase) ∧ z.regs 1062 = some (b32 13) ∧
        z.regs 2390 = some (b32 (l.sharedBase + 208)) ∧
        z.regs 6497 = some (b32 (l.sharedBase + 224)) ∧
        z.regs 1072 = some (b32 (g / l.block)) ∧
        z.regs 1178 = some (b32 (l.sharedBase + 68608)) ∧ z.regs 7228 = some (b32 p.batch) ∧
        z.regs 7502 = some (b64 p.cuQBase) ∧ z.regs 7506 = some (b64 p.cuQBase) ∧
        z.regs 7290 = some (.ptr 64 false (.param (param 10)) 0) ∧
        z.regs 1069 = some (b32 (l.sharedBase + 192)) ∧
        z.regs 6495 = some (b32 (l.sharedBase + 144)) ∧
        z.regs 7500 = some (b64 p.lseBase) ∧ z.regs 7501 = some (b64 p.lseStride) ∧
        z.regs 7503 = some (b64 p.usedKBase) := by
  obtain ⟨t, o, hpc, hf, hbase, hwarp, habi, hSub, hAcc, hrun⟩ := broadcastPrefix hpre hX g hg htr
  rw [hw] at hwarp
  obtain ⟨u, hr, hp, hfu, _, _, _, _, _, _, h144, h208, h192, _, h224, _, hSubU, hAccU, hframe⟩ :=
    nonzeroWarpWith (A := A) hpre g 13 t (by decide) (by decide) hpc hf hwarp hbase
  have hNext : Next kernel A l g t u (.fenceMbarInit (next u)) :=
    ⟨run_rtg hr, startupOut (.inl (by rw [hp]; decide)) (fenceOut hp hfu)⟩
  obtain ⟨hfence, hr'⟩ := fixedTail hNext (fun _ h => h.2) hrun
  let v := next u
  have hpv : v.pc = 173 := by change u.pc + 1 = 173; rw [hp]
  have hNext' : Next kernel A l g v v (.bar 0 (next v) none .sync) :=
    ⟨.refl, startupOut (.inl (by rw [hpv]; decide)) (barOut hpv hfu)⟩
  obtain ⟨hbar, hr''⟩ := fixedTail hNext' (fun _ h => h.2) hr'
  let w := next v
  have hpw : w.pc = 174 := by change v.pc + 1 = 174; rw [hpv]
  have hrw : w.regs = u.regs := rfl
  have hwarp' : w.regs 1062 = some (b32 13) :=
    (congrFun hrw 1062).trans ((hframe 1062 (by decide)).trans hwarp)
  have hbase' : w.regs 2535 = some (b32 l.sharedBase) :=
    (congrFun hrw 2535).trans ((hframe 2535 (by decide)).trans hbase)
  obtain ⟨z, hdispatch, hzp, hzf, hcta, hbuf, hbatch, hSubZ, hAccZ, hframe'⟩ :=
    warp13DispatchWith (A := A) hpre g w hg hpw hfu hwarp' hbase'
  have hfenceEvent : e₃ = ⟨172, .fenceMbarInit⟩ := hp ▸ hfence.1
  have hbarEvent : e₄ = ⟨173, .bar 0 none .sync⟩ := hpv ▸ hbar.1
  have kept (r : Nat) (h₂ : r ∉ [1072, 1706, 60, 1178, 263, 7228]) : z.regs r = u.regs r :=
    (hframe' r h₂).trans (congrFun hrw r)
  have keep (r : Nat) (h₁ : r ∉ [18, 19, 1063, 22, 1064, 1065, 27, 1066, 1067, 32, 1068,
      6495, 37, 42, 2390, 47, 1069, 1070, 52, 6497, 57, 1071])
      (h₂ : r ∉ [1072, 1706, 60, 1178, 263, 7228]) : z.regs r = t.regs r := by
    rw [kept r h₂, hframe r h₁]
  have abi (r : Nat) (v : Value) (hm : (r, v) ∈ abiFacts p l)
      (h₁ : r ∉ [18, 19, 1063, 22, 1064, 1065, 27, 1066, 1067, 32, 1068,
        6495, 37, 42, 2390, 47, 1069, 1070, 52, 6497, 57, 1071])
      (h₂ : r ∉ [1072, 1706, 60, 1178, 263, 7228]) : z.regs r = some v :=
    (keep r h₁ h₂).trans (holds_mem habi hm)
  exact ⟨hfenceEvent, hbarEvent, w, z, o, hr'', run_rtg hdispatch, hzp, hzf,
    hSubZ.trans (hSubU.trans hSub), hAccZ.trans (hAccU.trans hAcc),
    (hframe' 2535 (by decide)).trans hbase', (hframe' 1062 (by decide)).trans hwarp',
    (kept 2390 (by decide)).trans h208, (kept 6497 (by decide)).trans h224, hcta, hbuf, hbatch,
    abi 7502 _ (by simp [abiFacts]) (by decide) (by decide),
    abi 7506 _ (by simp [abiFacts]) (by decide) (by decide),
    abi 7290 _ (by simp [abiFacts]) (by decide) (by decide),
    (kept 1069 (by decide)).trans h192, (kept 6495 (by decide)).trans h144,
    abi 7500 _ (by simp [abiFacts]) (by decide) (by decide),
    abi 7501 _ (by simp [abiFacts]) (by decide) (by decide),
    abi 7503 _ (by simp [abiFacts]) (by decide) (by decide)⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue
