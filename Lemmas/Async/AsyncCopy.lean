-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.AsyncCopy
public import Mathlib.Logic.Relation

@[expose] public section

namespace PTX.AsyncCopy
noncomputable section

/-- Case analysis on a stage with the slot or target unfolded. -/
@[elab_as_elim, cases_eliminator]
def Part.casesFlat {motive : Part → Sort _}
    (readCopy : motive (.read .copy)) (readLoad : ∀ x y k, motive (.read (.load x y k)))
    (readStore : ∀ x y k, motive (.read (.store x y k))) (readCta : ∀ c, motive (.read (.cta c)))
    (readElem : ∀ j, motive (.read (.elem j)))
    (writeCopy : motive (.write .copy)) (writeLoad : ∀ x y k, motive (.write (.load x y k)))
   (writeStore : ∀ x y k, motive (.write (.store x y k)))
    (writeCta : ∀ c, motive (.write (.cta c)))
    (writeElem : ∀ j, motive (.write (.elem j)))
    (oldCopy : motive (.old .copy)) (oldLoad : ∀ x y k, motive (.old (.load x y k)))
    (oldStore : ∀ x y k, motive (.old (.store x y k))) (oldCta : ∀ c, motive (.old (.cta c)))
    (oldElem : ∀ j, motive (.old (.elem j)))
    (notifyCopy : motive (.notify .copy)) (notifyLoad : motive (.notify .load))
    (notifyCta : ∀ c, motive (.notify (.cta c)))
    (readsDone : motive .readsDone) (fullDone : motive .fullDone) (resolve : motive .resolve)
    (tcNotify : ∀ r, motive (.tcNotify r)) (mmaRead : ∀ b k, motive (.mmaRead b k))
    (mmaDone : motive .mmaDone) (arriveOn : motive .arriveOn)
    (readPrefetch : ∀ x y k, motive (.read (.prefetch x y k)))
    (writePrefetch : ∀ x y k, motive (.write (.prefetch x y k)))
    (oldPrefetch : ∀ x y k, motive (.old (.prefetch x y k))) : ∀ p, motive p
  | .read .copy => readCopy | .read (.load x y k) => readLoad x y k
  | .read (.store x y k) => readStore x y k | .read (.cta c) => readCta c
  | .read (.elem j) => readElem j
  | .write .copy => writeCopy | .write (.load x y k) => writeLoad x y k
  | .write (.store x y k) => writeStore x y k | .write (.cta c) => writeCta c
  | .write (.elem j) => writeElem j
  | .old .copy => oldCopy | .old (.load x y k) => oldLoad x y k
  | .old (.store x y k) => oldStore x y k | .old (.cta c) => oldCta c
  | .old (.elem j) => oldElem j
  | .notify .copy => notifyCopy | .notify .load => notifyLoad | .notify (.cta c) => notifyCta c
  | .readsDone => readsDone | .fullDone => fullDone | .resolve => resolve
  | .tcNotify r => tcNotify r | .mmaRead b k => mmaRead b k | .mmaDone => mmaDone
  | .arriveOn => arriveOn
  | .read (.prefetch x y k) => readPrefetch x y k | .write (.prefetch x y k) => writePrefetch x y k
  | .old (.prefetch x y k) => oldPrefetch x y k

/-- A copy that completes through its notification, writes its whole destination from memory and
has source and destination of the same size reads exactly the bytes it writes. -/
theorem CopyOk.completed {s : Spec} {e : Effects} (h : CopyOk s e) (hc : e.notified = true)
    (hd : s.data = none) (hw : s.writes = .whole) (hsz : s.src.size = s.dst.size) :
    ∃ bs, e.readBytes = some bs ∧ e.writeBytes = some bs ∧ bs.length = s.dst.size := by
  rcases h.2.2.2.1 hc with ⟨-, bs, hws⟩
  have hsrc : sourceBytes s e = some bs := by
    have := h.2.2.1 bs hws
    simpa [hw] using this
  simp only [sourceBytes, hd, Option.map_eq_some_iff, hsz, Nat.sub_self, List.replicate_zero,
    List.append_nil] at hsrc
  rcases hsrc with ⟨rs, hrs, heq⟩
  rw [← heq] at hws
  exact ⟨rs, hrs, hws, (h.2.1 rs hrs).2.trans hsz⟩

theorem Extends.refl (X : Snapshot) : Extends X X :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h,
    fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem Extends.trans {X Y Z : Snapshot} (hxy : Extends X Y) (hyz : Extends Y Z) :
    Extends X Z :=
  ⟨fun i bs h => hyz.1 i bs (hxy.1 i bs h),
    fun i bs h => hyz.2.1 i bs (hxy.2.1 i bs h),
    fun i h => hyz.2.2.1 i (hxy.2.2.1 i h),
    fun i values h => hyz.2.2.2.1 i values (hxy.2.2.2.1 i values h),
    fun i h => hyz.2.2.2.2.1 i (hxy.2.2.2.2.1 i h),
    fun i h => hyz.2.2.2.2.2.1 i (hxy.2.2.2.2.2.1 i h),
    fun i j bs h => hyz.2.2.2.2.2.2.1 i j bs (hxy.2.2.2.2.2.2.1 i j bs h),
    fun i j bs h => hyz.2.2.2.2.2.2.2 i j bs (hxy.2.2.2.2.2.2.2 i j bs h)⟩

/-- Preserving operand outcomes also preserves the fact that the MMA has started. -/
theorem Extends.mmaStarted {X Y : Snapshot} (hxy : Extends X Y) {i : EvId}
    (hs : X.mmaStarted i = true) : Y.mmaStarted i = true := by
  unfold Snapshot.mmaStarted at hs ⊢
  cases hx : X.mmaOperands i with
  | none => simp [hx] at hs
  | some values => rw [hxy.2.2.2.1 i values hx]; rfl

/-- Old completion notifications survive extension unchanged. -/
theorem Notification.extends {issued : EvId → Option Spec} {X Y : Snapshot}
    (hxy : Extends X Y) {i : EvId} {m : Loc} {n : Nat}
    (h : Notification issued X i m n) : Notification issued Y i m n := by
  obtain ⟨s, hi, hc, hm, hn⟩ := h
  exact ⟨s, hi, hxy.2.2.1 i hc, hm, hn⟩

end
end PTX.AsyncCopy
