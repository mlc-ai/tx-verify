-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mbar
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Mbar
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Mbar
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mbar

@[expose] public section

/-! # Which lanes use an mbarrier object, and how

`bar_use`: an event that names an object of lane `g`'s CTA and is no initialization is of a lane of
that CTA and one of the uses of its warp's role (`BarUse`, from the roles' `Export/Mbar`). A
theorem about who uses a barrier takes the cases of `BarUse` and compares offsets. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The uses of the object at offset `o` of lane `g`'s CTA by event `e` of lane `h` at `k`**, by
the role of the lane's warp. -/
inductive BarUse (L : Launch) (X : Execution) (g h k o : Nat) (e : Event) : Prop where
  | epiPoll (st : Fin 2) (ok : Bool) (hw : Prologue.warpIndex L h = 13) (ho : o = 208 + 8 * st.val)
      (hk : e.kind = .wait (obj L g o) 0 ok true .cta)
      (h0 : okPolls (obj L g o) ((X.tr h).take k) = 0)
  | epiArr (st : Fin 2) (hw : Prologue.warpIndex L h = 13) (ho : o = 224 + 8 * st.val)
      (hk : e.kind = .arrive (obj L g o) 0 1 true .cta)
      (h0 : arrivals (obj L g o) ((X.tr h).take k) = 0)
  | corrArr (hw : 8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11)
      (ho : o = 96 ∨ o = 104 ∨ o = 192 ∨ o = 200 ∨ o = 208 ∨ o = 216)
      (hk : e.kind = .arrive (obj L g o) 0 1 true .cta)
  | corrPoll (ok : Bool) (hw : 8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11)
      (ho : o = 144 ∨ o = 152 ∨ o = 224 ∨ o = 232)
      (hk : e.kind = .wait (obj L g o) ((okPolls (obj L g o) ((X.tr h).take k) + corrΔ o) % 2) ok
        true .cta)
  | softArr (a : Nat) (hw : Prologue.warpIndex L h < 8) (ha : a = 96 ∨ a = 112 ∨ a = 336)
      (ho : o = 8 * (Prologue.warpIndex L h / 4) + a)
      (hk : e.kind = .arrive (obj L g o) 0 1 true .cta)
  | softPoll (a : Nat) (ok : Bool) (hw : Prologue.warpIndex L h < 8)
      (ha : a = 80 ∨ a = 192 ∨ a = 320) (ho : o = 8 * (Prologue.warpIndex L h / 4) + a)
      (hk : e.kind = .wait (obj L g o) ((okPolls (obj L g o) ((X.tr h).take k) + softΔ a) % 2) ok
        true .cta)
  | mmaPoll (ok : Bool) (hw : Prologue.warpIndex L h = 12) (ho : MmaPollOff o)
      (hk : e.kind = .wait (obj L g o) (okPolls (obj L g o) ((X.tr h).take k) % 2) ok true .cta)
  | mmaCommit (s : TcCommit.Spec) (hw : Prologue.warpIndex L h = 12) (ho : MmaCommitOff o)
      (hk : e.kind = .tc (.commit s)) (hb : s.mbar = obj L g o) (hg : s.group = .one)
      (hel : ∃ j pc' inst, j < k ∧
        X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩)
  | ldPoll (par : Nat) (ok : Bool)
      (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) (ho : LdPollOff o)
      (hk : e.kind = .wait (obj L g o) par ok true .cta)
  | ldAsync (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
      (ho : o = 32 ∨ o = 40 ∨ o = 48) (hk : e.kind = .asyncArrive (obj L g o) true)
  | ldArr (tx : Nat) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
      (ho : LdTmaOff o) (hk : e.kind = .arrive (obj L g o) tx 1 true .cta)
  | ldCopy (a : Nat) (s : TensorCopy.Spec)
      (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
      (ho : LdTmaOff o) (hk : e.kind = .tensorIssue a s) (hb : s.mbar = obj L g o)

/-- **Every use of an object that is no initialization**: the lane is of the object's CTA and the
use is one of `BarUse`. -/
theorem bar_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k o : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hm : MbarOf e (obj L g o)) (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) :
    h / L.block = g / L.block ∧ BarUse L X g h k o e := by
  have h16 := Prologue.warpIndex_lt hp h
  rcases show Prologue.warpIndex L h < 8 ∨
      (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) ∨ Prologue.warpIndex L h = 12 ∨
      Prologue.warpIndex L h = 13 ∨
      (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) by omega with
    hw | hw | hw | hw | hw
  · rcases soft_mbar_use hp hX hFw hw he hm hni with ⟨a, ha, hl, hk⟩ | ⟨a, ok, ha, hl, hk⟩
    · obtain ⟨hc, ho⟩ := obj_off hl
      exact ⟨hc, .softArr a hw ha ho.symm hk⟩
    · obtain ⟨hc, ho⟩ := obj_off hl
      exact ⟨hc, .softPoll a ok hw ha ho.symm hk⟩
  · rcases corr_mbar_use hp hX hFw hw.1 hw.2 he hm hni with ⟨a, ha, hl, hk⟩ | ⟨a, ok, ha, hl, hk⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .corrArr hw ha hk⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .corrPoll ok hw ha hk⟩
  · rcases mma_mbar_use hp hX hFw hw he hm hni with ⟨a, ok, ha, hl, hk⟩ |
      ⟨a, s, ha, hl, hk, hb, hg, hel⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .mmaPoll ok hw ha hk⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .mmaCommit s hw ha hk hb hg hel⟩
  · rcases epi_mbar_use hp hX hFw hw he hm hni with ⟨st, ok, hl, hk, h0⟩ | ⟨st, hl, hk, h0⟩
    · obtain ⟨hc, ho⟩ := obj_off hl
      exact ⟨hc, .epiPoll st ok hw ho.symm hk h0⟩
    · obtain ⟨hc, ho⟩ := obj_off hl
      exact ⟨hc, .epiArr st hw ho.symm hk h0⟩
  · rcases ld_mbar_use hp hX hFw hw he hm hni with ⟨a, par, ok, ha, hl, hk⟩ | ⟨a, ha, hl, hk⟩ |
      ⟨a, tx, ha, hl, hk⟩ | ⟨a, ad, s, ha, hl, hk, hb⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .ldPoll par ok hw ha hk⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .ldAsync hw ha hk⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .ldArr tx hw ha hk⟩
    · obtain ⟨hc, rfl⟩ := obj_off hl
      exact ⟨hc, .ldCopy ad s hw ha hk hb⟩

/-- **Who names a barrier that only commits complete**: a poll, or an MMA lane's commit. -/
theorem commit_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k o : Nat} {e : Event}
    (ho : o = 16 ∨ o = 24 ∨ o = 56 ∨ o = 64 ∨ o = 72 ∨ o = 80 ∨ o = 88)
    (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) :
    (∃ par ok acq sc, e.kind = .wait (obj L g o) par ok acq sc) ∨
      ∃ s, e.kind = .tc (.commit s) ∧ Prologue.warpIndex L h = 12 ∧ s.mbar = obj L g o ∧
        ∃ j pc' inst, X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩ := by
  obtain ⟨-, hu⟩ := bar_use hp hX hFw he hm hni
  cases hu with
  | epiArr _ _ ho' | corrArr _ ho' | softArr _ _ _ ho' | ldAsync _ ho' => omega
  | ldArr _ _ ho' | ldCopy _ _ _ ho' => unfold LdTmaOff at ho'; omega
  | epiPoll _ ok _ _ hk | corrPoll ok _ _ hk | softPoll _ ok _ _ _ hk | mmaPoll ok _ _ hk
  | ldPoll _ ok _ _ hk => exact .inl ⟨_, ok, true, .cta, hk⟩
  | mmaCommit s hw _ hk hb _ hel =>
    obtain ⟨j, pc', inst, -, hj⟩ := hel
    exact .inr ⟨s, hk, hw, hb, j, pc', inst, hj⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
