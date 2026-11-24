-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairCompletion

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

/-- A recorded completion exposes the real predecessor readiness certificate. -/
theorem CompletionClosed.ready {L : Launch} {X : Execution} (hX : CompletionClosed L X)
    {ws : List WarpRequest} (hc : Completed X ws) : CompletionReady L X ws :=
  hX ws hc

/-- Warp request validity depends on source traces alone. -/
theorem completion_valid_trace_iff {L : Launch} {X Y : Execution}
    (htr : X.tr = Y.tr) (group : CtaGroup) (w : WarpRequest) :
    w.Valid L X group ↔ w.Valid L Y group := by
  simp only [WarpRequest.Valid, Execution.TcK, Execution.get, htr]

/-- The prefix property transports with real request validity, complete operations and
coverage. No memory or async fields are involved. -/
theorem completionClosed_frame {L : Launch} {X Y : Execution}
    (hvalid : ∀ (w : WarpRequest) group, w.Valid L Y group → w.Valid L X group)
    (hcompleted : ∀ ws, Completed Y ws → Completed X ws ∨ CompletionReady L X ws)
    (hcovered : ∀ i, Covered L X i → Covered L Y i)
    (hX : CompletionClosed L X) : CompletionClosed L Y := by
  intro ws hws w hw w' group hv hb i hp
  apply hcovered i
  rcases hcompleted ws hws with h | h
  · exact hX ws h w hw w' group (hvalid w' group hv) hb i hp
  · exact h w hw w' group (hvalid w' group hv) hb i hp

/-- Snapshot-only changes preserve the law without classifying their fields. -/
theorem completionClosed_of_trace {L : Launch} {X Y : Execution}
    (htr : X.tr = Y.tr) (hhistory : Y.tmemHistory = X.tmemHistory)
    (hpairing : Y.tmemPairing = X.tmemPairing)
    (hX : CompletionClosed L X) : CompletionClosed L Y := by
  apply completionClosed_frame (X := X) ?_ ?_ ?_ hX
  · intro w group hv
    exact (completion_valid_trace_iff htr group w).mpr hv
  · intro ws hws
    simp only [Completed, hhistory, hpairing] at hws
    exact .inl hws
  · intro i hi
    simpa only [Covered, Completed, hhistory, hpairing] using hi

end
end PTX.Tmem.Pair

namespace PTX
/-- Append one record to CTA `cta`'s allocator history. -/
def Execution.recordEntry (X : Execution) (cta : Nat) (r : Tmem.Pair.Requests) : Execution :=
  { X with tmemHistory := fun k => if k = cta then X.tmemHistory k ++ [r] else X.tmemHistory k }

/-- Append one pairing of two cta_group::2 warp requests. -/
def Execution.recordPairing (X : Execution) (q : Tmem.Pair.WarpRequest × Tmem.Pair.WarpRequest) :
    Execution :=
  { X with tmemPairing := X.tmemPairing ++ [q] }
end PTX

namespace PTX.Tmem.Pair
noncomputable section

theorem mem_recordEntry {X : Execution} {cta k : Nat} {r x : Requests}
    (h : x ∈ (X.recordEntry cta r).tmemHistory k) : x ∈ X.tmemHistory k ∨ (k = cta ∧ x = r) := by
  simp only [Execution.recordEntry] at h
  split_ifs at h with hk
  · rcases List.mem_append.mp h with h | h
    · exact .inl h
    · exact .inr ⟨hk, List.mem_singleton.mp h⟩
  · exact .inl h

theorem mem_recordEntry_old {X : Execution} {cta k : Nat} {r x : Requests}
    (h : x ∈ X.tmemHistory k) : x ∈ (X.recordEntry cta r).tmemHistory k := by
  simp only [Execution.recordEntry]
  split_ifs
  · exact List.mem_append_left _ h
  · exact h

/-- Pure record append frame: for a cta_group::1 record, its operation is ready. -/
theorem completionClosed_recordEntry {L : Launch} {X : Execution} {cta : Nat} {r : Requests}
    (hX : CompletionClosed L X) (hready : r.group = .one → CompletionReady L X [r.own]) :
    CompletionClosed L (X.recordEntry cta r) := by
  refine completionClosed_frame (X := X) (Y := X.recordEntry cta r)
    (fun _ _ h => h) ?_ ?_ hX
  · rintro ws (⟨k, x, hx, hg, rfl⟩ | ⟨q, hq, rfl⟩)
    · rcases mem_recordEntry hx with h | ⟨-, rfl⟩
      · exact .inl (.inl ⟨k, x, h, hg, rfl⟩)
      · exact .inr (hready hg)
    · exact .inl (.inr ⟨q, hq, rfl⟩)
  · rintro i ⟨ws, (⟨k, x, hx, hg, rfl⟩ | ⟨q, hq, rfl⟩), hw⟩
    · exact ⟨_, .inl ⟨k, x, mem_recordEntry_old hx, hg, rfl⟩, hw⟩
    · exact ⟨_, .inr ⟨q, hq, rfl⟩, hw⟩

/-- Pure pairing append frame: the paired operation is ready. -/
theorem completionClosed_recordPairing {L : Launch} {X : Execution}
    {q : WarpRequest × WarpRequest}
    (hX : CompletionClosed L X) (hready : CompletionReady L X [q.1, q.2]) :
    CompletionClosed L (X.recordPairing q) := by
  refine completionClosed_frame (X := X) (Y := X.recordPairing q)
    (fun _ _ h => h) ?_ ?_ hX
  · rintro ws (⟨k, x, hx, hg, rfl⟩ | ⟨q', hq, rfl⟩)
    · exact .inl (.inl ⟨k, x, hx, hg, rfl⟩)
    · rcases List.mem_append.mp hq with hq | hq
      · exact .inl (.inr ⟨q', hq, rfl⟩)
      · rw [List.mem_singleton.mp hq]
        exact .inr hready
  · rintro i ⟨ws, (⟨k, x, hx, hg, rfl⟩ | ⟨q', hq, rfl⟩), hw⟩
    · exact ⟨_, .inl ⟨k, x, hx, hg, rfl⟩, hw⟩
    · exact ⟨_, .inr ⟨q', List.mem_append_left _ hq, rfl⟩, hw⟩
end
end PTX.Tmem.Pair
