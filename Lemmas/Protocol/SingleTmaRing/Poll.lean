-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.Order

@[expose] public section

/-! # The phase a designated poll of a single-CTA ring barrier finds

A proof tool (generalized from the Inkling KV ring): the successful poll of the arrival or copy
thread of `empty` for use `n ≥ 1` found phase `n` completed, and the consumer's successful poll
of `full` for use `u` found phase `u + 1` (`producer_poll_phase`, `consumer_poll_phase`); a poll
of another thread with `c` earlier successful polls found a phase at least `c + δ` (resp.
`c + 1`) (`lane_poll_empty`, `lane_poll_full`). -/

namespace PTX.SingleTmaRing
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section

/-- A poll of parity `p` passes on a barrier `c` of whose phases are complete. -/
def Open (p c : Nat) : Prop := p % 2 = (c + 1) % 2


variable {X : Execution} {S : Slot} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {sc : MbarScope}

/-- **Any lane's successful poll of `full`.** -/
theorem lane_poll_full (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {g k pc p : Nat}
    {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait S.full p true acq sc⟩) :
    ∃ i w st, (X.objects S.full)[i]? = some w ∧ w.id = .thread (g, k) ∧
      stateBefore (X.objects S.full) i = some st ∧
      okPolls S.full ((X.tr g).take k) + 1 ≤ st.phase ∧ Open p st.phase := by
  have hlt := PairTmaRing.okPolls_lt_of_get he
  obtain ⟨i, w, p', hi, hwid, ha, hww, hwf, hcnt⟩ :=
    MbarRing.Poll.record hX (full_poll_clean hX H) hlt
  have hnth : MbarRing.Poll.nth X S.full g (okPolls S.full ((X.tr g).take k)) = k :=
    MbarRing.Poll.nth_eq he
  rw [hnth] at hwid
  have hs : objectThreadSelected g w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hge, hpar⟩ := (X.objects_checked hX S.full).selected_poll_phase_ge
    H.full_noInval (objectThreadSelected g) (by omega : 0 ≤ 1) (F_alt hX H g) hi hs hww
  have hpp := H.full_parity he
  refine ⟨i, w, st, hi, hwid, hst, by omega, ?_⟩
  unfold Open
  omega

end
end PTX.SingleTmaRing
