-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueExitLoop
public import Kernels.TmlFa4Fwd.Proof.SchedulerDrainWords
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {l : Launch}

/-- Warp 13's first drain read uses the same boundary and input table as its initial scan. -/
theorem drainFirstEvent {m : Mem0} {A : List Assumption} (hp : Pre p l m) (g : Nat) (t : TState)
    (hModel : ∀ {s : TState}, 2986 ≤ s.pc → s.pc ≤ 2990 → out kernel A l g s = out kernel [] l g s)
    (hpc : t.pc = 2986) (hf : t.fault = none)
    (hGate : t.regs 307 = some (.pred (p.batch < laneOf l g)))
    (hIndex : t.regs 1201 = some (b32 (laneOf l g))) (hBase : t.regs 7506 = some (b64 p.cuQBase))
    (hZero : t.regs 7229 = some (b32 0)) :
    let lane := laneOf l g
    let src := b32 (drainCuQ p lane)
    (p.batch < lane ∧ ∃ u, u = { t with pc := 2990 } ∧
      Next kernel A l g t u (.shfl .down src 1 31 (fun v _ => next (setReg u 2401 v)))) ∨
    (lane ≤ p.batch ∧ ∃ u, u.pc = 2989 ∧ u.sub = 0 ∧ u.acc = [] ∧ u.fault = none ∧
      (∀ r, r ≠ 7872 → r ≠ 7873 → u.regs r = t.regs r) ∧
      Next kernel A l g t u
        (.read {loc := globalLoc (p.cuQBase + 4 * lane), size := 4} (afterLoad u [7229]))) := by
  dsimp only
  have hBranch := drainScanBranch (p := p) hpc hf hGate
  have hStep : tauStep kernel A l g t = tauStep kernel [] l g t := by
    rw [tauStep, hModel (by omega) (by omega), ← tauStep]
  by_cases h : p.batch < laneOf l g
  · let u := { t with pc := 2990 }
    have ht : run kernel A l g 1 t = some u := by
      simpa [run, hStep, h, u] using hBranch
    refine .inl ⟨h, u, rfl, run_rtg ht, ?_⟩
    have hU : u.pc = 2990 := rfl
    rw [hModel (s := u) (by omega) (by omega)]
    simpa [drainCuQ, Nat.not_le_of_lt h, b32] using drainFirstShuffle hp g u 0 rfl hf hZero
  · have hs : run kernel A l g 1 t = some (skip t) := by
      simpa [run, hStep, h] using hBranch
    have hSkip : (skip t).pc = 2987 := by simp [skip, hpc]
    have hn := Nat.le_of_not_lt h
    obtain ⟨u, hRead, hu, huf, hus, hua, hFrame, hOut⟩ :=
      drainLaneRead hp g (skip t) hn (fun hlo hhi => hModel (by omega) (by omega))
        hSkip hf rfl rfl hIndex hBase
    exact .inr ⟨hn, u, hu, hus, hua, huf, hFrame, run_rtg (run_comp hs hRead), hOut⟩

/-- The cuQ read continues into the same collective, with the bytes provided by `Pre.cuQ`. -/
theorem drainAfterRead {m : Mem0} {A : List Assumption} (hp : Pre p l m) (g : Nat) (t : TState)
    (hModel : ∀ {s : TState}, s.pc = 2990 → out kernel A l g s = out kernel [] l g s)
    (hpc : t.pc = 2989) (hs : t.sub = 0) (ha : t.acc = []) (hf : t.fault = none) :
    let word := b32 (drainCuQ p (laneOf l g))
    let u := afterLoad t [7229] (word.toBytes.map some)
    u.pc = 2990 ∧ u.sub = 0 ∧ u.acc = [] ∧ u.fault = none ∧
      u.regs 7229 = some word ∧ (∀ r, r ≠ 7229 → u.regs r = t.regs r) ∧
      out kernel A l g u =
        .ev (.shfl .down word 1 31 (fun v _ => next (setReg u 2401 v))) := by
  dsimp only
  have hRead := rebuild_scalar (v := b32 (drainCuQ p (laneOf l g)))
    (show 0 < 4 by decide) rfl
  have hEq : afterLoad t [7229] ((b32 (drainCuQ p (laneOf l g))).toBytes.map some) =
      next (setReg t 7229 (b32 (drainCuQ p (laneOf l g)))) := by
    rw [afterLoad_ok hs ha hRead]
    simp [next, setReg, hs, ha]
  rw [hEq]
  have hu : (next (setReg t 7229 (b32 (drainCuQ p (laneOf l g))))).pc = 2990 := by
    change t.pc + 1 = 2990
    rw [hpc]
  refine ⟨hu, hs, ha, hf, by simp [next, setReg], ?_, ?_⟩
  · intro r hr
    simp [next, setReg, hr]
  · rw [hModel hu]
    exact drainFirstShuffle hp g _ _ hu hf (by simp [next, setReg, b32])

/-- A read action on this path obtains the launch word once all of its bytes are protected
from writes. This connects the event template to the memory-model observation. -/
theorem drainReadValue {m : Mem0} {A : List Assumption} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) (g : Nat) (i : EvId) (bs : List (Option Byte))
    (hn : laneOf l g ≤ p.batch)
    (hRead : X.get i =
      some ⟨2989, .rd {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} bs⟩)
    (hProtected : ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * laneOf l g)).at k)) :
    bs = (b32 (drainCuQ p (laneOf l g))).toBytes.map some := by
  have hMemRead : X.MemReads (.thread i)
      {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} bs :=
    .inl ⟨2989, hRead⟩
  apply hX.launch_value hMemRead rfl hProtected
  simpa [drainCuQ, hn, b32, HasValue, Value.bytes] using hp.cuQ (laneOf l g) hn

/-- In an accepted trace the first down shuffle receives the immutable cumulative-length
operand, with the optional read accounting for one extra event in participating lanes. -/
theorem drainFirstTrace {m : Mem0} {A : List Assumption} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) (g j : Nat) (t : TState)
    (hModel : ∀ {s : TState}, 2986 ≤ s.pc → s.pc ≤ 2990 → out kernel A l g s = out kernel [] l g s)
    (hpc : t.pc = 2986) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hGate : t.regs 307 = some (.pred (p.batch < laneOf l g)))
    (hIndex : t.regs 1201 = some (b32 (laneOf l g))) (hBase : t.regs 7506 = some (b64 p.cuQBase))
    (hZero : t.regs 7229 = some (b32 0)) {e e' : Event} {rest : List Event} {o : Option TState}
    (hTrace : (X.tr g).drop j = e :: e' :: rest) (hRun : Run kernel A l g t (e :: e' :: rest) o)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * laneOf l g)).at k)) :
    let idx := if laneOf l g ≤ p.batch then j + 1 else j
    let word := b32 (drainCuQ p (laneOf l g))
    (laneOf l g ≤ p.batch → X.get (g, j) = some ⟨2989,
      .rd {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} (word.toBytes.map some)⟩) ∧
    ∃ recv ok u, X.get (g, idx) = some ⟨2990, .shfl .down word 1 31 recv ok⟩ ∧
      At u 2991 [(7229, word), (2401, recv)] ∧
      (∀ r, r ∉ [7872, 7873, 7229, 2401] → u.regs r = t.regs r) ∧
      Run kernel A l g u ((X.tr g).drop (idx + 1)) o := by
  let word := b32 (drainCuQ p (laneOf l g))
  have shflCont {a b : TState} {f : Event} {es : List Event}
      (hb : At b 2990 [(7229, word)])
      (hFrame : ∀ r, r ∉ [7872, 7873, 7229, 2401] → b.regs r = t.regs r)
      (hs : Next kernel A l g a b (.shfl .down word 1 31 (fun v _ => next (setReg b 2401 v))))
      (hr : Run kernel A l g a (f :: es) o) :
      ∃ recv ok u, f = ⟨2990, .shfl .down word 1 31 recv ok⟩ ∧
        At u 2991 [(7229, word), (2401, recv)] ∧
        (∀ r, r ∉ [7872, 7873, 7229, 2401] → u.regs r = t.regs r) ∧
        Run kernel A l g u es o := by
    have hn : ¬ Fires b.pc (.shfl .down word 1 31 (fun v _ => next (setReg b 2401 v))) f none := by
      rintro ⟨_, _, _, hbad⟩
      cases hbad
    obtain ⟨u, ⟨recv, ok, hEq, hout⟩, hz⟩ := hs.continuing_event hn hr
    obtain rfl := Option.some.inj hout
    refine ⟨recv, ok, _, by simpa only [hb.1] using hEq, ?_, ?_, hz⟩
    · have hAt := hb.set (r := 2401) (v := recv) (by simp)
      exact hAt.mono ⟨hAt.2.2.2.2.2.1, hAt.2.2.2.2.1, trivial⟩
    · intro r hr
      have hn : r ≠ 2401 := fun h => hr (by simp [h])
      simpa [next, setReg, hn] using hFrame r hr
  have hEvent : X.get (g, j) = some e := by
    change (X.tr g)[j]? = some e
    calc
      _ = ((X.tr g).drop j)[0]? := by rw [List.getElem?_drop, Nat.add_zero]
      _ = some e := by rw [hTrace]; rfl
  dsimp only
  rcases drainFirstEvent hp g t hModel hpc hf hGate hIndex hBase hZero with
    ⟨hLane, b, rfl, hNext⟩ | ⟨hLane, b, hb, hsub, hacc, hbf, hFrame, hNext⟩
  · have hb : At {t with pc := 2990} 2990 [(7229, word)] := by
      refine ⟨rfl, hs, ha, hf, ?_⟩
      simpa [word, drainCuQ, Nat.not_le_of_lt hLane, Holds] using hZero
    obtain ⟨recv, ok, u, he, hu, hr, hRest⟩ := shflCont hb (fun _ _ => rfl) hNext hRun
    rw [ite_eq_right (Nat.not_le_of_lt hLane)]
    have hDrop : (X.tr g).drop (j + 1) = e' :: rest := by
      rw [← List.drop_drop, hTrace]
      rfl
    exact ⟨fun h => (Nat.not_le_of_lt hLane h).elim, recv, ok, u,
      hEvent.trans (congrArg some he), hu, hr, hDrop ▸ hRest⟩
  · let a : Acc := {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
    have hn : ¬ Fires b.pc (.read a (afterLoad b [7229])) e none := by
      rintro ⟨_, _, _, hi⟩
      cases hi
    obtain ⟨v, ⟨bs, _, he, hu⟩, hTail⟩ := hNext.continuing_event hn hRun
    obtain rfl := Option.some.inj hu
    have hx : X.get (g, j) = some ⟨2989, .rd a bs⟩ := by
      rw [he, hb] at hEvent
      exact hEvent
    have hBytes := drainReadValue hp hX g (g, j) bs hLane hx (hProtected hLane)
    subst bs
    obtain ⟨hpv, hsv, hav, hfv, hWord, hFrameRd, hOut⟩ :=
      drainAfterRead hp g b (fun hs => hModel (by omega) (by omega)) hb hsub hacc hbf
    obtain ⟨recv, ok, u, he', hpu, hreg, hRest⟩ :=
      shflCont ⟨hpv, hsv, hav, hfv, hWord, trivial⟩ (by
        intro r hr
        have h₂ : r ≠ 7872 := fun h => hr (by simp [h])
        have h₃ : r ≠ 7873 := fun h => hr (by simp [h])
        have h₄ : r ≠ 7229 := fun h => hr (by simp [h])
        exact (hFrameRd r h₄).trans (hFrame r h₂ h₃)) ⟨.refl, hOut⟩ hTail
    rw [ite_eq_left hLane]
    have hGet : X.get (g, j + 1) = some e' := by
      change (X.tr g)[j + 1]? = some e'
      calc
        _ = ((X.tr g).drop j)[1]? := by rw [List.getElem?_drop]
        _ = some e' := by rw [hTrace]; rfl
    have hDrop : (X.tr g).drop (j + 1 + 1) = rest := by
      rw [show j + 1 + 1 = j + 2 by omega, ← List.drop_drop, hTrace]
      rfl
    exact ⟨fun _ => hx, recv, ok, u, hGet.trans (congrArg some he'), hpu, hreg, hDrop ▸ hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
