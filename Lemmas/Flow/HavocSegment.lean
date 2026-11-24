-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Havoc
public import Lemmas.Flow.SegLane

@[expose] public section

namespace PTX.Flow.Havoc
open PTX.Assumption

variable {σ : Type} [DecidableEq σ]

/-- Include clobbered temporaries, outputs and constants initialized by a defining instance. -/
def ofMatch (m : SegMatch σ) : Hook where
  stop := m.stop
  writes := m.shape.writes.map m.regOf ++ m.shape.io.map (fun p => m.regOf p.2) ++
    (if m.shape.defines then m.shape.consts.map (fun p => m.regOf p.1) else [])

private theorem mapM_keys {α β : Type} (key : α → Nat) (f : α → Exec (Nat × β))
    (hf : ∀ a p, f a = .ok p → p.1 = key a) (xs : List α) {ys : List (Nat × β)}
    (h : xs.mapM f = .ok ys) : ys.map Prod.fst = xs.map key := by
  induction xs generalizing ys with
  | nil => cases h; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error => simp only [hx, bind, Except.bind] at h; cases h
    | ok p =>
      cases hs : xs.mapM f with
      | error => simp only [hx, hs, bind, Except.bind] at h; cases h
      | ok ps =>
        simp only [hx, hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst ys
        simp only [List.map_cons, hf _ _ hx, ih hs]

/-- The register frame of the template's actual register effect. -/
private theorem frame {m : SegMatch σ} {t : TState} {ys : List (Nat × Value)}
    (hk : ys.map Prod.fst = m.shape.io.map (fun p => m.regOf p.2)) {r : Nat}
    (hr : r ∉ (ofMatch m).writes) : segRegs m t ys r = t.regs r := by
  simp only [ofMatch, List.mem_append, not_or] at hr
  refine segRegs_keep (fun s hs h => hr.1.1 (h ▸ List.mem_map_of_mem hs)) ?_ ?_
  · intro p hp he
    apply hr.1.2
    rw [← hk, ← he]
    exact List.mem_map_of_mem hp
  · intro hd p hp he
    apply hr.2
    simp only [hd, ↓reduceIte, ← he]
    exact List.mem_map_of_mem hp

/-- A lane reader may fail on either lane. Every successful execution has the same footprint. -/
theorem execSegmentLane_frame {m : SegMatch σ} {t u : TState} {lane : Value → Exec ℝ}
    (h : execSegmentLane lane m t = .ok u) :
    u.pc = m.stop ∧ u.sub = 0 ∧ u.acc = [] ∧ u.fault = t.fault ∧ u.cf = t.cf ∧
    ∀ r, r ∉ (ofMatch m).writes → u.regs r = t.regs r := by
  classical
  let f := fun p : σ × σ => do
    let v ← readReg t (m.regOf p.1)
    let x ← lane v
    pure (m.regOf p.2, Value.float .f32 x)
  have keys (p : σ × σ) (q) (he : f p = .ok q) : q.1 = m.regOf p.2 := by
    unfold f at he
    cases hv : readReg t (m.regOf p.1) with
    | error => simp only [hv, bind, Except.bind] at he; cases he
    | ok v =>
      cases hx : lane v with
      | error => simp only [hv, hx, bind, Except.bind] at he; cases he
      | ok x =>
        simp only [hv, hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he
        cases he
        rfl
  unfold execSegmentLane at h
  dsimp only at h
  split at h
  · change (m.shape.io.mapM f >>= fun ys =>
      pure { t with regs := segRegs m t ys, pc := m.stop, sub := 0, acc := [] }) = .ok u at h
    cases hy : m.shape.io.mapM f with
    | error => simp only [hy, bind, Except.bind] at h; cases h
    | ok ys =>
      simp only [hy, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst u
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => frame (mapM_keys _ f keys _ hy)⟩
  · cases h

theorem execSegment_frame {m : SegMatch σ} {t u : TState} {fn : ℝ → ℝ}
    (h : execSegment fn m t = .ok u) :
    u.pc = m.stop ∧ u.sub = 0 ∧ u.acc = [] ∧ u.fault = t.fault ∧ u.cf = t.cf ∧
    ∀ r, r ∉ (ofMatch m).writes → u.regs r = t.regs r := by
  apply execSegmentLane_frame (lane := fun v => fn <$> valFloat .f32 v)
  simpa only [execSegmentLane, execSegment, bind_map_left] using h

end PTX.Flow.Havoc
