-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

/-!
# Instances of the masked warp collectives

The instances of `vote.sync` with a mode, `redux.sync` and `match.sync`, which wait for the
non-exited lanes of their member mask.

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## DEP-WARP-INSTANCE — instances of a masked warp collective

Statement: In each lane, the n-th execution of a masked warp collective with member mask m belongs
  to the n-th instance of that collective and mask in the warp. Every lane of the mask either takes
  part in the instance with the same qualifiers and the same mask, or has exited before reaching it,
  and the inputs of the instance are those of the lanes that take part. A lane returns from an
  instance only after every lane of the mask has executed its event of the instance or exited.

Defs: warpSize, maskInWarp, WarpPart, Execution.MaskK, MaskExited, MaskInstance, laneBits,
  Execution.MaskExitK, Execution.MaskAt, MaskWait, maskExited_iff, MaskWait.ret, MaskWait.src

Source:
- §9.7.15.10: "vote.sync will cause executing thread to wait until all non-exited threads
    corresponding to membermask have executed vote.sync with the same qualifiers and same membermask
    value before resuming execution."
- §9.7.15.11: "match.sync will cause executing thread to wait until all non-exited threads from
    membermask have executed match.sync with the same qualifiers and same membermask value before
    resuming execution."
- §9.7.15.13: "redux.sync will cause the executing thread to wait until all non-exited threads
    corresponding to membermask have executed redux.sync with the same qualifiers and same
    membermask value before resuming execution."
- EXT-WARP-INSTANCE

Direction: reading

Applies: Instances of `vote.sync` with mode `.all`, `.any` or `.uni` (DEP-WARP-VOTE), of the integer
  `redux.sync` forms (DEP-WARP-REDUX) and of `match.sync` (DEP-WARP-MATCH)

Premises: An event of the collective exists at a given per-mask ordinal.

Effect: Instance membership and inputs, used by VoteModeOk, VoteOk, ReduxOk and MatchOk; the
  waiting dependency `MaskWait`, from which `KindNeeds` (DEP-ORDER) takes the needs of
  `shfl.sync`, `vote.sync`, `redux.sync` and `match.sync`. A class `c` maps the event kind of a
  collective to what the lane contributes (`WarpPart`): its member mask, the qualifiers that the
  lanes of one instance share, and its input. `MaskK` numbers the events of a class with one member
  mask within a thread; it is the one instance identification of these collectives, used by their
  value rules and by their needs alike. The instance of the `n`-th events of mask `m` in the warp of
  thread `g` assigns each lane its input (`part`): the input of its `n`-th event, which has the same
  qualifiers and mask, for a lane that takes part, and none for a lane of the mask that exited
  before its `n`-th event and for every lane outside the mask. The thread rules give these
  collectives a rule only when every lane named in the mask is a thread of the warp (`maskInWarp`),
  so a lane of the mask is always a thread of the launch. Lanes may reach an instance from
  different source positions, as for `shfl.sync`. The quoted sentences make every lane of the
  instance wait: a lane resumes only after each non-exited lane of the mask has executed the
  instruction with the same qualifiers and the same mask. `MaskWait` states this waiting
  dependency. It relates, within the warp, the `n`-th event with mask `m` and the same qualifiers of
  every lane, and the exit of every lane of the mask that exited before its `n`-th such event
  (`Execution.MaskExitK`), to the return of the `n`-th event of each lane: a lane of the mask that
  has not exited when another lane waits has not exited for that wait, so the wait ends at its
  arrival or at its exit. A lane whose `n`-th event has other qualifiers fills no need, so no
  consistent execution contains the waiting event (`DependencyOk.ready`). Two lanes that reach two
  instances in opposite orders, such as a `vote.sync` followed by a `redux.sync` in one lane and the
  reverse in the other, form a cycle of the dependency order that `DependencyOk.acyclic` excludes:
  no consistent execution contains both returns, the execution stays incomplete and the kernel's
  progress obligation fails, as on hardware, where both lanes wait forever. The dependency is part
  of the execution layer only and orders no memory operation.

### EXT-WARP-INSTANCE — the n-th executions with one member mask form one instance

Statement: The lanes of a member mask pair their executions of a masked warp collective by order: in
  every lane, the n-th execution of the collective with member mask m belongs to the n-th instance
  of that collective and mask. An instance of `vote.sync`, `redux.sync` or `match.sync` with member
  mask m contains, for each lane of m that has not exited, that lane's n-th execution of the
  instruction with member mask m; executions with other member masks belong to other instances.

Source:
- §9.7.15.10
- §9.7.15.11 and §9.7.15.13, as quoted in DEP-WARP-INSTANCE

Why it is not spec text: The text says what an executing thread waits for. Read literally, an
  execution that another lane completed earlier with the same mask would satisfy the wait. The text
  does not say that each execution of a lane takes part in exactly one instance together with one
  execution of every other non-exited lane of the mask, which is the pairing that the results of
  these instructions ("the same across all threads in membermask" for `vote.sync`) presuppose.

Direction: reading

Effect: If a hardware instance paired other executions, the inputs, and so the results, the model
  assigns would differ from the hardware's. Pairing by order with one mask is the only pairing in
  which every execution of a lane takes part in one instance with every other non-exited lane of the
  mask and no two lanes reach two instances in opposite orders. Disclosed by every kernel whose
  statement names `VoteMode.all`, `VoteMode.any`, `VoteMode.uni`, `VoteMode.ballot`,
  `WarpKind.redux` or `WarpKind.match_`: FlashAttn4Fwd, FlashMlaSparseDecodeH64.
-/

/-- The number of threads of the warp of thread `g`: 32, or fewer in the last warp of a CTA whose
size is not a multiple of 32. -/
def warpSize (g : Nat) : Nat := min 32 (L.block - g % L.block / 32 * 32)

/-- Every lane named in member mask `m` is a thread of the warp of thread `g`. -/
def maskInWarp (g m : Nat) : Prop := m < 2 ^ warpSize L g

instance (g m : Nat) : Decidable (maskInWarp L g m) := by unfold maskInWarp; infer_instance

/-- What one lane contributes to a masked warp collective: its member mask, the qualifiers that
the lanes of one instance share, and its input. -/
structure WarpPart (Q V : Type) where
  mask : Nat
  qual : Q
  input : V

namespace Execution

variable (X : Execution)

/-- `e` is an event of class `c` with member mask `m`, and the thread performed `n` events of
class `c` with mask `m` before it. -/
def MaskK {Q V : Type} (c : Kind → Option (WarpPart Q V)) (e : EvId) (m n : Nat) : Prop :=
  (∃ ev p, X.get e = some ev ∧ c ev.kind = some p ∧ p.mask = m) ∧
    ((X.tr e.1).take e.2).countP (fun ev => (c ev.kind).any (·.mask == m)) = n

end Execution

/-- Thread `h` exited after at most `n` events of class `c` with member mask `m`: it never
performs its `n`-th such event. -/
def MaskExited {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (h m n : Nat) :
    Prop :=
  ∃ k pc, X.get (h, k) = some ⟨pc, .exit⟩ ∧
    ((X.tr h).take k).countP (fun ev => (c ev.kind).any (·.mask == m)) ≤ n

/-- The instance of the `n`-th events of class `c` with member mask `m` in the warp of thread `g`,
with qualifiers `q`: `part lane` is the input of a lane of the mask that takes part, and none for
a lane of the mask that exited before its `n`-th event and for a lane outside the mask. -/
def MaskInstance {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (g m n : Nat)
    (q : Q) (part : Nat → Option V) : Prop :=
  ∀ lane < 32,
    (m.testBit lane = true →
      (∃ j pc k v, X.get (g - laneOf L g + lane, j) = some ⟨pc, k⟩ ∧ c k = some ⟨m, q, v⟩ ∧
        X.MaskK c (g - laneOf L g + lane, j) m n ∧ part lane = some v) ∨
      (MaskExited c X (g - laneOf L g + lane) m n ∧ part lane = none)) ∧
    (m.testBit lane = false → part lane = none)

/-- `e` is the exit of a thread that performed at most `n` events of class `c` with member mask
`m` before it: the thread exited before its `n`-th such event. -/
def Execution.MaskExitK {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (e : EvId)
    (m n : Nat) : Prop :=
  (∃ pc, X.get e = some ⟨pc, .exit⟩) ∧
    ((X.tr e.1).take e.2).countP (fun ev => (c ev.kind).any (·.mask == m)) ≤ n

theorem maskExited_iff {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution)
    (h m n : Nat) : MaskExited c X h m n ↔ ∃ k, X.MaskExitK c (h, k) m n := by
  constructor
  · rintro ⟨k, pc, he, hc⟩; exact ⟨k, ⟨pc, he⟩, hc⟩
  · rintro ⟨k, ⟨pc, he⟩, hc⟩; exact ⟨k, pc, he, hc⟩

/-- `e` is the `n`-th event of class `c` with member mask `m` of its thread, with qualifiers `q`. -/
def Execution.MaskAt {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (e : EvId)
    (m n : Nat) (q : Q) : Prop :=
  X.MaskK c e m n ∧ ∃ ev p, X.get e = some ev ∧ c ev.kind = some p ∧ p.qual = q

/-- The waiting dependency of an instance of class `c` (DEP-WARP-INSTANCE): `f` is the `n`-th
event of class `c` with member mask `m` and qualifiers `q` of its thread, and `e`, of the same
warp, is the `n`-th such event of its thread with the same qualifiers, or the exit of a lane of the
mask that exited before its `n`-th such event. The return of `f` waits for `e`. -/
def MaskWait {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (e f : EvId) :
    Prop :=
  SameWarp L e.1 f.1 ∧ ∃ m n q, X.MaskAt c f m n q ∧
    (X.MaskAt c e m n q ∨ (m.testBit (laneOf L e.1) = true ∧ X.MaskExitK c e m n))

/-- The return of a waiting dependency is an event of the class. -/
theorem MaskWait.ret {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X : Execution}
    {e f : EvId} (h : MaskWait L c X e f) : ∃ pc k p, X.get f = some ⟨pc, k⟩ ∧ c k = some p := by
  obtain ⟨-, m, n, q, ⟨⟨⟨⟨pc, k⟩, p, hg, hc, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨pc, k, p, hg, hc⟩

/-- The source of a waiting dependency is an event of the class or an exit. -/
theorem MaskWait.src {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X : Execution}
    {e f : EvId} (h : MaskWait L c X e f) :
    (∃ pc k p, X.get e = some ⟨pc, k⟩ ∧ c k = some p) ∨ ∃ pc, X.get e = some ⟨pc, .exit⟩ := by
  obtain ⟨-, m, n, q, -, ⟨⟨⟨⟨pc, k⟩, p, hg, hc, -⟩, -⟩, -⟩ | ⟨-, he, -⟩⟩ := h
  · exact .inl ⟨pc, k, p, hg, hc⟩
  · exact .inr he

/-- The 32-bit mask whose bit `lane` is set exactly when `f lane` holds. -/
def laneBits (f : Nat → Bool) : BitVec 32 :=
  BitVec.ofNat 32 (((List.range 32).filter f).foldr (fun lane acc => acc + 2 ^ lane) 0)

end

end PTX
