-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Data.Events
public import Core.Sync.WarpInstance

@[expose] public section

/-!
# Shuffle events and values

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## THREAD-SHFL — warp shuffle
Statement: `shfl.sync` in any mode on a 32-bit value, with the full member mask in a CTA whose size
  is a multiple of 32, produces a shuffle event with the lane's operands. The received value is
  determined by DEP-WARP-SHUFFLE. Other masks have no rule, and an operand of another size is a type
  fault.

Defs: shflTmpl

Source:
- §9.7.10.6 (shfl.sync)

Direction: stricter

Applies: Full-mask `shfl.sync.{up,down,bfly,idx}.b32`

Premises: The CTA size is a multiple of 32, the member mask is full, and operands pass type checks.

Effect: Event production.
-/

/-- Warp shuffle (SHFL). -/
def shflTmpl (L : Launch) (g : Nat) (t : TState) (mode : ShflMode) (d : Nat)
    (p : Option Nat) (a b c mask : Opnd) : Tmpl :=
  match readBits L g t 32 mask, readValue L g t 32 a, readBits L g t 32 b,
      readBits L g t 32 c with
  | .ok m, .ok av, .ok bv, .ok cv =>
    if m.toNat = 2 ^ 32 - 1 ∧ L.block % 32 = 0 then
      if av.bytes = 4 then
        .shfl mode av bv.toNat cv.toNat (fun recv ok =>
          let t1 := setReg t d recv
          next (match p with | some p => setReg t1 p (.pred ok) | none => t1))
      else .ub .typeMismatch
    else .ub .noRule
  | .error f, _, _, _ | _, .error f, _, _ | _, _, .error f, _ | _, _, _, .error f => .ub f

/-! ## DEP-WARP-SHUFFLE — warp shuffle instances

Statement: The n-th shuffles of the lanes of a warp form one instance, and every lane of the warp
  either takes part in it with the same mode or has exited before reaching it. A lane receives the
  operand of its source lane, which the pseudo-code of the instruction computes from the lane number
  and the `b` and `c` operands, together with the validity predicate. The value received from a
  source lane that exited is unconstrained. A lane returns from an instance only after every lane of
  the warp has executed its shuffle of the instance or exited.

Defs: shflSource, Execution.ShflK, ShflExited, ShflOk, shflClass, maskK_shflClass,
  maskExitK_shflClass

Source:
- §9.7.10.6 (shfl.sync): "wait until all non-exited threads corresponding to membermask have
    executed shfl.sync with the same qualifiers and same membermask value before resuming execution"
- §9.7.10.6 (shfl.sync): "results are undefined if a thread sources a register from an inactive
    thread or a thread that is not in membermask"
- §9.7.10.6 (shfl.sync): "case .up: j = lane - bval; pval = (j >= maxLane); break; case .down: j =
    lane + bval; pval = (j <= maxLane); break;"
- §9.7.10.6 (shfl.sync): "if (!pval) j = lane; // copy from own lane"
- EXT-SHFL-UP-INDEX

Direction: reading

Applies: Full-member-mask shuffle instances

Premises: A shuffle event exists at a given ordinal.

Effect: Execution constraint in `Consistent.shfl` (the received values); the waiting dependency
  `MaskWait L shflClass` (DEP-WARP-INSTANCE) gives the needs of a shuffle in `KindNeeds`
  (DEP-ORDER), so a shuffle exists in a consistent execution only when every lane of the warp
  has executed its shuffle of the instance with the same mode or exited. The `n`-th shuffles of the
  lanes of a warp form one instance. A lane whose guard is false performs no shuffle event; an
  instance therefore never contains a predicated-off lane, and executions in which lanes that may
  execute one `shfl.sync` together evaluate its guard differently are unsafe
  (ERR-NONUNIFORM-GUARD), so no predicated-off lane is paired into a later instance. Lanes may reach
  it from different source positions (sm_70 and later), and their `b`, `c` operands are their own. A
  lane that exited before its `n`-th shuffle does not take part; a value read from such a source
  lane is unconstrained. The waiting dependency of an instance is the one of DEP-WARP-INSTANCE for
  the class `shflClass`, whose member mask is the full mask: the shuffle of every lane of the warp,
  and the exit of every lane that exited before its `n`-th shuffle, precede the return of each
  shuffle of the `n`-th instance. `ShflK` is the class ordinal `MaskK shflClass` with the full mask,
  which `maskK_shflClass` proves, so the value rule and the needs pair the same executions.
  `maskK_shflClass` and `maskExitK_shflClass` restate the class in terms of `ShflK` and the exits of
  `ShflExited`.

### EXT-SHFL-UP-INDEX — the source lane of `shfl.sync.up` is an integer difference

Statement: In `.up` mode the source lane index `lane - bval` is an integer, so a lane whose number
  is smaller than `bval` has no source lane: its predicate is false and it receives its own operand.
  `shflSource .up lane b c` is in range only when `b % 32 ≤ lane` and the maximum lane of the
  segment is at most `lane - b % 32`; otherwise the lane copies its own operand with predicate
  false.

Source:
- §9.7.10.6: "lane[4:0] = [Thread].laneid;"
- §9.7.10.6: "bval[4:0] = b[4:0];"
- §9.7.10.6: "case .up: j = lane - bval; pval = (j >= maxLane); break;"
- §9.7.10.6: "If the computed source lane index j is in range, the thread will copy the input
    operand a from lane j into its own destination register d ; otherwise, the thread will simply
    copy its own input a to destination d ."

Why it is not spec text: The pseudo-code declares `lane` and `bval` as 5-bit fields and does not
  declare `j`. If `j` were a 5-bit field, `lane - bval` would wrap for a lane below `bval` and name
  a lane at the top of the warp, which `pval` would then compare with `maxLane`. The model takes the
  integer difference, which is below every `maxLane` for such a lane.

Direction: reading

Effect: If the hardware wrapped the index, a lane below `bval` would receive another lane's operand
  with predicate true, and the values the model derives for it would differ from the hardware's.
  Disclosed by every kernel whose statement names `ShflMode.up`: none.
-/

/-- Source lane and validity of `shfl.sync` (PTX ISA, `shfl.sync` pseudo-code). -/
def shflSource (mode : ShflMode) (lane b c : Nat) : Nat × Bool :=
  let bval := b % 32
  let clamp := c % 32
  let seg := c / 256 % 32
  let maxLane := (lane &&& seg) ||| (clamp &&& (31 - seg))
  match mode with
  | .up => if bval ≤ lane ∧ maxLane ≤ lane - bval then (lane - bval, true) else (lane, false)
  | .down => if lane + bval ≤ maxLane then (lane + bval, true) else (lane, false)
  | .bfly | .idx =>
    let j := match mode with
      | .bfly => lane ^^^ bval
      | _ => (lane &&& seg) ||| (bval &&& (31 - seg))
    if j ≤ maxLane then (j, true) else (lane, false)

namespace Execution

variable (X : Execution)

/-- `e` is the `n`-th shuffle of its thread. -/
def ShflK (e : EvId) (n : Nat) : Prop :=
  (∃ pc m a b c r o, X.get e = some ⟨pc, .shfl m a b c r o⟩) ∧
    ((X.tr e.1).take e.2).countP isShfl = n

end Execution


/-- Lane `h` exited without reaching its `n`-th shuffle. -/
def ShflExited (X : Execution) (h n : Nat) : Prop :=
  ∃ k pc, X.get (h, k) = some ⟨pc, .exit⟩ ∧ ((X.tr h).take k).countP Execution.isShfl ≤ n

/-- Every shuffle event received what the `shfl.sync` pseudo-code delivers: the validity predicate,
and the operand of the source lane's shuffle of the same instance, or any value when the source
lane exited before it. That every lane of the warp took part or exited is the need of the shuffle
(`KindNeeds`, DEP-ORDER). -/
def ShflOk (X : Execution) : Prop :=
  ∀ g i n pc m a b c recv ok, X.get (g, i) = some ⟨pc, .shfl m a b c recv ok⟩ →
    X.ShflK (g, i) n →
    ok = (shflSource m (laneOf L g) b c).2 ∧
    ((∃ j pc' b' c' r' o', X.ShflK (g - laneOf L g + (shflSource m (laneOf L g) b c).1, j) n ∧
      X.get (g - laneOf L g + (shflSource m (laneOf L g) b c).1, j) =
        some ⟨pc', .shfl m recv b' c' r' o'⟩) ∨
      ShflExited X (g - laneOf L g + (shflSource m (laneOf L g) b c).1) n)

/-- The `shfl.sync` class (DEP-WARP-INSTANCE): a shuffle contributes the full member mask, its
mode and its operand. -/
def shflClass : Kind → Option (WarpPart ShflMode Value)
  | .shfl mode a _ _ _ _ => some ⟨2 ^ 32 - 1, mode, a⟩
  | _ => none

private theorem shflClass_count (m : Nat) :
    (fun ev : Event => (shflClass ev.kind).any (·.mask == m)) =
      fun ev => Execution.isShfl ev && m == 2 ^ 32 - 1 := by
  funext ev
  obtain ⟨pc, k⟩ := ev
  cases k <;> simp [shflClass, Execution.isShfl, eq_comm]

/-- The `n`-th event of class `shflClass` with mask `m` is the `n`-th shuffle, and `m` is the full
mask. -/
theorem maskK_shflClass (X : Execution) (e : EvId) (m n : Nat) :
    X.MaskK shflClass e m n ↔ m = 2 ^ 32 - 1 ∧ X.ShflK e n := by
  unfold Execution.MaskK Execution.ShflK
  rw [shflClass_count]
  constructor
  · rintro ⟨⟨⟨pc, k⟩, p, hg, hc, rfl⟩, hn⟩
    cases k <;> simp [shflClass] at hc
    obtain ⟨-, rfl⟩ := hc
    exact ⟨rfl, ⟨_, _, _, _, _, _, _, hg⟩, by simpa using hn⟩
  · rintro ⟨rfl, ⟨pc, md, a, b, c, r, o, hg⟩, hn⟩
    exact ⟨⟨_, _, hg, rfl, rfl⟩, by simpa using hn⟩

/-- An exit of class `shflClass` with mask `m` before the `n`-th event is an exit before the
`n`-th shuffle (`ShflExited`), when `m` is the full mask. -/
theorem maskExitK_shflClass (X : Execution) (h k n : Nat) :
    X.MaskExitK shflClass (h, k) (2 ^ 32 - 1) n ↔
      ∃ pc, X.get (h, k) = some ⟨pc, .exit⟩ ∧
        ((X.tr h).take k).countP Execution.isShfl ≤ n := by
  unfold Execution.MaskExitK
  rw [shflClass_count]
  simp

end

end PTX
