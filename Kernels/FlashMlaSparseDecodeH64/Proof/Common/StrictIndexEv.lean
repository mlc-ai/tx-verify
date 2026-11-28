-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndex
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Lemmas.Flow.StrictWindow

@[expose] public section

/-! # An event at an index state

An event of a followed lane that is no undefined behaviour, at an index state, is the site's event
(`ix_evAt`), the lane passes the gate of the index warp and has made at least three shuffles. The
loads and shuffles of the index warp are at pcs of its code (`ix_pcRange`, `ix_shflPc`). -/

/-! # The index warp's strict window along a trace

`ix_windowAt`: `ix_window` (`Common/StrictIndex.lean`) for a lane's trace: from the state before the
head's shuffle (position `k0`) to the state before event `i`, when the events from `k0` up to `i`
are well formed (`IxWfT`), the state `σ` before `i` satisfies `IxOk` and is strictly good with the
tag invariant, and fires its event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The window along a lane's trace.** -/
theorem ix_windowAt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hgate : subOk L g .index = true) {k0 i : Nat} {n0 : Cls → Nat}
    (hk0 : Frame.stateAt (thread P L) X g k0 = some (some (hshState P L g n0))) (hlt : k0 < i)
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) {e' : Event}
    (hn : (X.tr g)[i]? = some e')
    (hW : ∀ e ∈ ((X.tr g).drop k0).take (i - k0), IxWfT P e) :
    IxOk P L g σ ∧ ∃ t1 o', (thread P L g).Good (some σ) t1 ∧ QT ixQt t1 ∧
      EStep kernel Assumptions.all L g t1 e' o' := by
  obtain ⟨o0, hr⟩ := hX.thr g hg
  obtain ⟨m', hm'⟩ : ∃ m', i = k0 + (m' + 1) := ⟨i - k0 - 1, by omega⟩
  have hi : i - k0 = m' + 1 := by omega
  rw [hi] at hW
  have hafter2 : (thread P L g).toMachine.after (some (hshState P L g n0))
      (((X.tr g).drop k0).take (m' + 1)) = some (some σ) := by
    have h1 : (thread P L g).toMachine.after (some (thread P L g).init) ((X.tr g).take i) =
        some (some σ) := hσ
    have h2 : (X.tr g).take i = (X.tr g).take k0 ++ ((X.tr g).drop k0).take (m' + 1) := by
      rw [hm', ← List.take_add]
    rw [h2] at h1
    have h3 := Machine.after_append (thread P L g).toMachine (some (thread P L g).init)
      ((X.tr g).take k0) (((X.tr g).drop k0).take (m' + 1))
    replace h1 := h3.symm.trans h1
    rw [show (thread P L g).toMachine.after (some (thread P L g).init) ((X.tr g).take k0) =
      some (some (hshState P L g n0)) from hk0] at h1
    exact h1
  rw [hm'] at hn
  exact ix_window hp hr (Code.reach_init (thread_sound hp)) hk0 hgate ⟨n0, rfl⟩ hW hafter2 hn

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The event at an index state is the site's**, the gate passes and three shuffles are made. -/
theorem ix_evAt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) {d : Index.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n))) :
    Index.Ev P L g d e ∧ subOk L g .index = true ∧ 3 ≤ n .shfl := by
  obtain ⟨σ, hσ', hJ, -, hev, -⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  obtain ⟨-, hR, -, -⟩ := hJ
  obtain ⟨h3, hgate, -⟩ : 3 ≤ n .shfl ∧ subOk L g .index = true ∧
      (n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))) := hR
  exact ⟨hev, hgate, h3⟩

/-- A site whose event is no exit is at a pc of the index code. -/
theorem ix_pcRange {d : Index.D} {e : Event} (hev : Index.Ev P L g d e) (hne : e.kind ≠ .exit) :
    2332 ≤ e.pc ∧ e.pc < 2587 := by
  obtain ⟨h1, h2⟩ := hev
  rw [h1]
  obtain ⟨site, el, ac, c⟩ := d
  cases site <;> simp [IxSite.pc] at h2 ⊢
  all_goals exact absurd h2 hne

/-- **A shuffle of the index warp is at one of its four shuffle sites.** -/
theorem ix_shflSite {d : Index.D} {e : Event} (hev : Index.Ev P L g d e) {md : ShflMode}
    {a : Value} {b c : Nat} {r : Value} {ok : Bool} (hk : e.kind = .shfl md a b c r ok) :
    d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .sB1 ∨ d.site = .sB2 := by
  obtain ⟨-, h2⟩ := hev
  obtain ⟨site, el, ac, c⟩ := d
  cases site <;> simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
    Index.StoreEv, hk] at h2 ⊢

/-- The pcs of the four shuffle sites. -/
theorem ix_shflPc {d : Index.D} {e : Event} (hev : Index.Ev P L g d e)
    (hs : d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .sB1 ∨ d.site = .sB2) :
    e.pc = 2464 ∨ e.pc = 2467 ∨ e.pc = 2553 ∨ e.pc = 2556 := by
  rw [hev.1]
  rcases hs with h | h | h | h <;> rw [h] <;> simp [IxSite.pc]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
