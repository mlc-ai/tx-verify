-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # A thread's successful polls are at most the object's phase plus its offset

`MbarRing.Unit.Obj.okPolls_le` for any object: when the object's polls do not fault, no record
invalidates it, and thread `g`'s successful polls of it have the parity of their count plus `δ`
(`δ ≤ 1`), the final phase is at least the one `g`'s last successful poll found, so `g`'s
successful polls are at most the final phase plus `δ` (`okPolls_le_phase`). Promoted from
tml-fa4's `Proof2/Lib/PollLe.lean` (lane T1). -/

namespace PTX.MbarRing

open AsyncCopy MBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A thread's successful polls are at most the final phase plus its offset.** -/
theorem okPolls_le_phase (hX : Consistent L K A mem0 X) {m : Loc} {g δ : Nat} (hδ : δ ≤ 1)
    (hpclean : ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none)
    (hni : NoInval (X.objects m))
    (hpar : ∀ k pc p acq sc, X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
      p % 2 = (Flow.okPolls m ((X.tr g).take k) + δ) % 2)
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    Flow.okPolls m (X.tr g) ≤ before.phase + δ := by
  have hch := X.objects_checked hX m
  rcases Nat.eq_zero_or_pos (Flow.okPolls m (X.tr g)) with h0 | hpos
  · omega
  obtain ⟨k, w, -, hk, hwid, -, hww, -, hsel⟩ := MbarRing.Poll.record hX hpclean
    (show Flow.okPolls m (X.tr g) - 1 < Flow.okPolls m (X.tr g) by omega)
  have hs : objectThreadSelected g w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨sw, hsw, hge, -⟩ := hch.selected_poll_phase_ge hni _ hδ
    (MbarRing.Poll.alternates hX hpclean hpar) hk hs hww
  obtain ⟨t, ht, hle⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hk).1.le le_rfl hsw
  rw [hst] at ht
  cases ht
  rw [hsel] at hge
  omega

end PTX.MbarRing
