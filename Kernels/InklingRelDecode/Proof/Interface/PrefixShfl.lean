-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixPro
public import Kernels.InklingRelDecode.Proof.Thread.WorkerPre

@[expose] public section

/-!
# The worker's broadcast of the warp index does not leave the run

The worker's `shfl` state is the broadcast of the warp index (a full-warp `shfl.sync.idx` from
lane 0). Its machine follows the thread only when the received word is the thread's warp index.
By DEP-WARP-SHUFFLE (`Consistent.shfl`) the received word is the operand of lane 0's shuffle of
the same instance, or any value when lane 0 exited before reaching it.

The instance is the thread's first shuffle (`own_count`): the worker's first three events are
`bar.sync 0`, the base word's load and `bar.sync 0`. For lane 0 nothing is assumed about its
loaded values: its machine follows it through these four events for any value (it can only fault,
and a faulted thread performs no shuffle and no exit), so its first shuffle is its fourth event and
its operand is its warp index (`first_shfl`), and it cannot exit before it (`not_exited0`). The
proof uses only lane 0's own trace and machine, no fact of another thread's values, so it holds in
every consistent execution: `worker_shfl_next_ne` is `hnext` at the worker's `shfl` state.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Worker (preRank)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The first state of a worker thread is the worker's first site. -/
theorem init_w {g : Nat} (hd : ¬ IsDefault L g) :
    St Q L X g 0 = some (some (.w (.worker (Worker.D.start (Worker.startPro Q))))) := by
  show Frame.stateAt (code L Q) X g 0 = _
  rw [Frame.stateAt_zero]
  have h : ¬ g % L.block < 128 := hd
  simp [h]

theorem init_d {g : Nat} (hd : IsDefault L g) {w : WComp.WSt} :
    St Q L X g 0 ≠ some (some (.w w)) := by
  show Frame.stateAt (code L Q) X g 0 ≠ _
  rw [Frame.stateAt_zero]
  have h : g % L.block < 128 := hd
  simp [h]

/-- **A state at the worker's site of rank `r` is the thread's state before its `r`-th event.** -/
theorem w_pre_rank {g : Nat} :
    ∀ k, k ≤ (X.tr g).length → ∀ {w : Worker.D} {r : Nat},
      St Q L X g k = some (some (.w (.worker w))) → preRank w.site = some r → k = r := by
  intro k
  induction k with
  | zero =>
    intro _ w r hσ hr
    by_cases hd : IsDefault L g
    · exact absurd hσ (init_d hd)
    · rw [init_w hd] at hσ
      simp only [Option.some.injEq, TSt.w.injEq, WComp.WSt.worker.injEq] at hσ
      subst hσ
      simp [Worker.D.start, preRank] at hr
      exact hr
  | succ k ih =>
    intro hk w r hσ hr
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs := Frame.stateAt_succ (C := code L Q) he
    rw [show Frame.stateAt (code L Q) X g (k + 1) = some (some (.w (.worker w))) from hσ] at hs
    cases hk' : St Q L X g k with
    | none => rw [show Frame.stateAt (code L Q) X g k = none from hk'] at hs; cases hs
    | some σ =>
      rw [show Frame.stateAt (code L Q) X g k = some σ from hk'] at hs
      cases σ with
      | none => cases hs
      | some s =>
        have hs' : (threadCode L g Q).next s e = some (some (.w (.worker w))) := hs.symm
        cases s with
        | d s =>
          rw [next_d] at hs'
          obtain ⟨a, -, ha⟩ := map_map_eq_some_some hs'
          cases ha
        | w s =>
          rw [next_w] at hs'
          obtain ⟨a, ha, hae⟩ := map_map_eq_some_some hs'
          cases hae
          cases r with
          | zero => exact absurd hr (WComp.pre_tgt_zero ha)
          | succ r =>
            obtain ⟨w0, rfl, hr0⟩ := WComp.pre_tgt ha hr
            have := ih (by omega) hk' hr0
            omega

/-- **The first four states of a worker thread**: the state before its `i`-th event (`i ≤ 3`)
is the worker's site of rank `i`, or the machine has stopped at a fault. -/
theorem w_pre_fwd {g : Nat} (hd : ¬ IsDefault L g) :
    ∀ i, i ≤ 3 → i ≤ (X.tr g).length →
      (∃ w, St Q L X g i = some (some (.w (.worker w))) ∧ preRank w.site = some i) ∨
        St Q L X g i = none := by
  intro i
  induction i with
  | zero =>
    intro _ _
    exact Or.inl ⟨_, init_w hd, rfl⟩
  | succ i ih =>
    intro h3 hl
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs := Frame.stateAt_succ (C := code L Q) he
    rcases ih (by omega) (by omega) with ⟨w, hw, hr⟩ | hn
    · rw [show Frame.stateAt (code L Q) X g i = some (some (.w (.worker w))) from hw] at hs
      have hs' : St Q L X g (i + 1) = (threadCode L g Q).next (.w (.worker w)) e := hs
      rw [next_w] at hs'
      rcases WComp.pre_next (L := L) (g := g) (e := e) hr (by omega) with h | ⟨w', h, hr'⟩
      · right
        rw [hs', h]
        rfl
      · left
        refine ⟨w', ?_, hr'⟩
        rw [hs', h]
        rfl
    · right
      rw [show Frame.stateAt (code L Q) X g i = none from hn] at hs
      exact hs

/-- Lane 0 of the warp of a thread is a thread of its warp. -/
theorem lane0_sameWarp (hb : L.block = 256) {g : Nat} (hg : g < L.threads) :
    SameWarp L g (g - laneOf L g + 0) := by
  have hthr : L.threads = L.grid * 256 := by
    unfold Launch.threads
    rw [hb]
  unfold SameWarp SameCta laneOf
  rw [hb]
  rw [hthr] at hg ⊢
  refine ⟨⟨hg, ?_, ?_⟩, ?_⟩ <;> omega

section
variable (hX : Consistent L kernel asms mem0 X) (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
  (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
include hX hS

/-- The events of the worker's sites of rank below 3 are neither shuffles nor exits. -/
theorem w_pre_ev {g k r : Nat} {w : Worker.D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.w (.worker w)))) (hr : preRank w.site = some r)
    (h3 : r < 3) : Execution.isShfl e = false ∧ e.kind ≠ .exit := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  exact WComp.pre_fires (L := L) (g := g) hr h3 hc hf

include hT in
/-- The event of the worker's `shfl` state is the broadcast of the thread's warp index. -/
theorem w_shfl_ev {g k : Nat} {P : Loader.Pro} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.w (.worker ⟨.shfl, P⟩)))) :
    ∃ pc recv ok, e = ⟨pc, .shfl .idx (b32 (Worker.warpOf L g)) 0 31 recv ok⟩ := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  obtain ⟨t, ins, hat, -, hc, hf⟩ := Frame.fired_site_of hS hg hF
  obtain ⟨recv, ok, h⟩ := WComp.shfl_fires (Q := Q) (atD_w.mp hat) hc hf
  exact ⟨_, recv, ok, h⟩

include hT in
/-- **Before a worker thread's first shuffle**: an event that is not undefined behaviour and has
no shuffle before it is one of the worker's first four events, fired from the site of its rank. -/
theorem w_prefix {g j : Nat} {e : Event} (hg : g < L.threads) (hd : ¬ IsDefault L g)
    (he : X.get (g, j) = some e) (hu : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hc : ((X.tr g).take j).countP Execution.isShfl = 0) :
    j ≤ 3 ∧ ∃ w, St Q L X g j = some (some (.w (.worker w))) ∧ preRank w.site = some j := by
  have hjl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hlive : ∀ {i}, i ≤ j → St Q L X g i ≠ none := by
    intro i hi hn
    have hn' := Frame.stateAt_none_mono hn hi
    rcases Frame.fired hS hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
    · rw [show Frame.stateAt (code L Q) X g j = none from hn'] at hσ
      cases hσ
    · exact hu pc f rfl
  by_cases hj3 : j ≤ 3
  · rcases w_pre_fwd (Q := Q) (X := X) hd j hj3 (by omega) with h | h
    · exact ⟨hj3, h⟩
    · exact absurd h (hlive le_rfl)
  · exfalso
    rcases w_pre_fwd (Q := Q) (X := X) hd 3 le_rfl (by omega) with ⟨w, hw, hr⟩ | h
    · obtain ⟨s, P⟩ := w
      cases s <;> simp only [preRank, Option.some.injEq, reduceCtorEq] at hr <;>
        (try omega)
      obtain ⟨e3, he3⟩ : ∃ e3, (X.tr g)[3]? = some e3 :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨pc, recv, ok, rfl⟩ := w_shfl_ev hX hS hT hg he3 hw
      have hmem : (⟨pc, .shfl .idx (b32 (Worker.warpOf L g)) 0 31 recv ok⟩ : Event) ∈
          (X.tr g).take j := by
        rw [List.mem_iff_getElem?]
        exact ⟨3, by rw [List.getElem?_take]; simp [show 3 < j by omega, he3]⟩
      have := (List.countP_pos_iff (p := Execution.isShfl)).mpr ⟨_, hmem, rfl⟩
      omega
    · exact hlive (by omega) h

include hT in
/-- **Lane 0's first shuffle has its warp index as operand.** -/
theorem first_shfl {g j : Nat} (hg : g < L.threads) (hd : ¬ IsDefault L g)
    (hk : X.ShflK (g, j) 0) :
    ∃ pc recv ok, X.get (g, j) = some ⟨pc, .shfl .idx (b32 (Worker.warpOf L g)) 0 31 recv ok⟩ := by
  obtain ⟨⟨pc, m, a, b, c, r, o, hget⟩, hcnt⟩ := hk
  obtain ⟨hj3, w, hw, hr⟩ := w_prefix hX hS hT hg hd hget (fun _ _ h => by cases h) hcnt
  by_cases h3 : j < 3
  · have := (w_pre_ev hX hS hget hw hr h3).1
    simp [Execution.isShfl] at this
  · have hj : j = 3 := by omega
    subst hj
    obtain ⟨s, P⟩ := w
    cases s <;> simp only [preRank, Option.some.injEq, reduceCtorEq] at hr <;> (try omega)
    obtain ⟨pc', recv, ok, h⟩ := w_shfl_ev hX hS hT hg hget hw
    exact ⟨pc', recv, ok, by rw [hget, h]⟩

include hT in
/-- **A worker thread does not exit before its first shuffle.** -/
theorem not_exited0 {g : Nat} (hg : g < L.threads) (hd : ¬ IsDefault L g) :
    ¬ ShflExited X g 0 := by
  rintro ⟨k, pc, hget, hcnt⟩
  have hc : ((X.tr g).take k).countP Execution.isShfl = 0 := by omega
  obtain ⟨hk3, w, hw, hr⟩ := w_prefix hX hS hT hg hd hget (fun _ _ h => by cases h) hc
  by_cases h3 : k < 3
  · exact (w_pre_ev hX hS hget hw hr h3).2 rfl
  · have hk : k = 3 := by omega
    subst hk
    obtain ⟨s, P⟩ := w
    cases s <;> simp only [preRank, Option.some.injEq, reduceCtorEq] at hr <;> (try omega)
    obtain ⟨pc', recv, ok, h⟩ := w_shfl_ev hX hS hT hg hget hw
    cases h

/-- A worker state is a state of a worker thread. -/
theorem w_not_default {g k : Nat} {w : WComp.WSt} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.w w))) : ¬ IsDefault L g := by
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX he hσ
  exact hinv.1

/-- **The worker's broadcast is its first shuffle.** -/
theorem own_count {g k : Nat} {P : Loader.Pro} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.w (.worker ⟨.shfl, P⟩)))) :
    ((X.tr g).take k).countP Execution.isShfl = 0 := by
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hd := w_not_default hX hS he hσ
  have hk3 : k = 3 := w_pre_rank k (by omega) hσ rfl
  subst hk3
  rw [List.countP_eq_zero]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi3 : i < 3 := by simp at hi; omega
  have hil : i < (X.tr g).length := by omega
  rw [List.getElem_take]
  rcases w_pre_fwd (Q := Q) (X := X) hd i (by omega) (by omega) with ⟨w, hw, hr⟩ | hn
  · have he' : X.get (g, i) = some (X.tr g)[i] := List.getElem?_eq_getElem hil
    have := (w_pre_ev hX hS he' hw hr hi3).1
    simp [this]
  · have := Frame.stateAt_none_mono (C := code L Q) hn (show i ≤ 3 by omega)
    rw [show Frame.stateAt (code L Q) X g 3 = some (some (.w (.worker ⟨.shfl, P⟩))) from hσ]
      at this
    cases this

include hT in
/-- **`hnext` at the worker's broadcast of the warp index**: the received word is the warp index,
so the worker's machine goes on to the dispatch loop's head. -/
theorem worker_shfl_next_ne (hpre : Pre Q L mem0) {g k : Nat} {P : Loader.Pro} {e : Event}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e)
    (hσ : St Q L X g k = some (some (.w (.worker ⟨.shfl, P⟩)))) :
    (threadCode L g Q).next (.w (.worker ⟨.shfl, P⟩)) e ≠ some none := by
  have he' : X.get (g, k) = some e := he
  have hd := w_not_default hX hS he' hσ
  obtain ⟨pc, recv, ok, rfl⟩ := w_shfl_ev hX hS hT hg he' hσ
  have hcnt := own_count hX hS he' hσ
  have hK : X.ShflK (g, k) 0 := ⟨⟨_, _, _, _, _, _, _, he'⟩, hcnt⟩
  obtain ⟨-, hsrc⟩ := hX.shfl g k 0 pc .idx _ 0 31 recv ok he' hK
  have h0 : (shflSource .idx (laneOf L g) 0 31).1 = 0 := by
    simp [shflSource]
  rw [h0] at hsrc
  have hb : L.block = 256 := hpre.block
  have hw := lane0_sameWarp hb hg
  have hh : g - laneOf L g + 0 < L.threads := hw.1.2.1
  have hwarp : Worker.warpOf L (g - laneOf L g + 0) = Worker.warpOf L g := hw.2.symm
  have hdh : ¬ IsDefault L (g - laneOf L g + 0) := by
    intro h
    apply hd
    have h1 : (g - laneOf L g + 0) % L.block / 32 = g % L.block / 32 := hw.2.symm
    unfold IsDefault at h ⊢
    omega
  have hrecv : recv = b32 (Worker.warpOf L g) := by
    rcases hsrc with ⟨j, pc', b', c', r', o', hK', hget'⟩ | hx
    · obtain ⟨pc'', recv'', ok'', hget''⟩ := first_shfl hX hS hT hh hdh hK'
      rw [hget''] at hget'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.shfl.injEq] at hget'
      rw [← hwarp]
      exact hget'.2.2.1.symm
    · exact absurd hx (not_exited0 hX hS hT hh hdh)
  subst hrecv
  rw [next_w]
  simp [WComp.next, Worker.next, b32]

end

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
