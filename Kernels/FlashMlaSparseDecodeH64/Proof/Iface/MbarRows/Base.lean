-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # The mbarrier classification rows: vocabulary

The words the rows of `Iface/MbarRows/<Role>.lean` are written in.

* **Lanes and objects.** `MbarRow.warp L g` is the thread's warp (`%tid.x / 32`) and
  `MbarRow.loc L g f` the mbarrier of family `f` in the thread's CTA.
* **Prefix counts.** Over a thread's events before its `k`-th (`(X.tr g).take k`): its successful
  polls on the two or four slots of a ring family (`polls2`, `polls4`), its arrivals on them
  (`arrs2`, `arrs4`) and its `tcgen05.commit`s addressing them (`cmts2`). `slot2 c` and `slot4 c`
  are the slot a count selects (`c % 2`, `c % 4`).
* **Uses.** `Wait e l q`: a CTA-scoped acquire poll of `l` with parity `q`; `Arrive e l tx`: one
  release arrival on `l` expecting `tx` bytes; `Commit e l`: a `tcgen05.commit` of CTA group 1
  whose addressed mbarrier is `l`; `Issue e l n`: a tensor load completing on `l` that moves `n`
  bytes.
* **The static check.** `mbarOp` selects the operations whose events can name an mbarrier,
  `Shape.ok` an operation's shape at a site, and `regionOk code lo hi sites` decides that the
  instructions of `[lo, hi)` that `mbarOp` selects are exactly the unguarded `sites`, each of its
  shape. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- The thread's warp (`%tid.x / 32`). -/
def warp (L : Launch) (g : Nat) : Nat := (L.tidOf g).x / 32

/-- The mbarrier of family `f` in the CTA of thread `g`. -/
abbrev loc (L : Launch) (g : Nat) (f : MbarFam) : Loc := mbarLoc L (g / L.block) f

/-- Whether `e` is a `tcgen05.commit` addressing `m`. -/
def commitsTo (m : Loc) (e : Event) : Bool :=
  match e.kind with
  | .tc (.commit s) => decide (s.mbar = m)
  | _ => false

/-- The slot of a two-slot ring that count `c` selects. -/
def slot2 (c : Nat) : Fin 2 := ⟨c % 2, Nat.mod_lt _ (by decide)⟩

/-- The slot of a four-slot ring that count `c` selects. -/
def slot4 (c : Nat) : Fin 4 := ⟨c % 4, Nat.mod_lt _ (by decide)⟩

/-- The successful polls of `es` on the two slots of family `F` in thread `g`'s CTA. -/
def polls2 (L : Launch) (g : Nat) (F : Fin 2 → MbarFam) (es : List Event) : Nat :=
  okPolls (loc L g (F 0)) es + okPolls (loc L g (F 1)) es

/-- The successful polls of `es` on the four slots of family `F` in thread `g`'s CTA. -/
def polls4 (L : Launch) (g : Nat) (F : Fin 4 → MbarFam) (es : List Event) : Nat :=
  okPolls (loc L g (F 0)) es + okPolls (loc L g (F 1)) es + okPolls (loc L g (F 2)) es +
    okPolls (loc L g (F 3)) es

/-- The arrivals of `es` on the two slots of family `F` in thread `g`'s CTA. -/
def arrs2 (L : Launch) (g : Nat) (F : Fin 2 → MbarFam) (es : List Event) : Nat :=
  arrivals (loc L g (F 0)) es + arrivals (loc L g (F 1)) es

/-- The arrivals of `es` on the four slots of family `F` in thread `g`'s CTA. -/
def arrs4 (L : Launch) (g : Nat) (F : Fin 4 → MbarFam) (es : List Event) : Nat :=
  arrivals (loc L g (F 0)) es + arrivals (loc L g (F 1)) es + arrivals (loc L g (F 2)) es +
    arrivals (loc L g (F 3)) es

/-- The `tcgen05.commit`s of `es` addressing the two slots of family `F` in thread `g`'s CTA. -/
def cmts2 (L : Launch) (g : Nat) (F : Fin 2 → MbarFam) (es : List Event) : Nat :=
  es.countP (commitsTo (loc L g (F 0))) + es.countP (commitsTo (loc L g (F 1)))

/-! ### The uses -/

/-- A CTA-scoped acquire poll of `l` with parity `q` (successful or not). -/
def Wait (e : Event) (l : Loc) (q : Nat) : Prop := ∃ ok, e.kind = .wait l q ok true .cta

/-- One CTA-scoped release arrival on `l` expecting `tx` bytes. -/
def Arrive (e : Event) (l : Loc) (tx : Nat) : Prop := e.kind = .arrive l tx 1 true .cta

/-- A `tcgen05.commit` of CTA group 1 whose addressed mbarrier is `l`. -/
def Commit (e : Event) (l : Loc) : Prop :=
  ∃ s : TcCommit.Spec, e.kind = .tc (.commit s) ∧ s.mbar = l ∧ s.group = .one

/-- A tensor load completing on `l` that moves `n` bytes. -/
def Issue (e : Event) (l : Loc) (n : Nat) : Prop :=
  ∃ (a : Nat) (s : TensorCopy.Spec), e.kind = .tensorIssue a s ∧ s.mbar = l ∧
    TensorTransfer.bytes s.descriptor = n

/-! ### The static check -/

/-- The operations whose events can name an mbarrier (`MbarOf`): initializations,
invalidations, arrivals, polls, tensor loads, `tcgen05.commit`, bulk copies, `cp.async`
arrivals, cluster launch control requests and asynchronous stores. -/
def mbarOp : Op → Bool
  | .mbarInit .. | .mbarInval .. | .mbarArrive .. | .mbarWait .. | .cpTensor .. | .tcCommit ..
  | .cpBulk .. | .cpAsyncArrive .. | .clcTryCancel .. | .asyncStore .. => true
  | _ => false

/-- The shape of an mbarrier site's operation. -/
inductive Shape where
  /-- `mbarrier.init` with a register count. -/
  | init
  /-- `mbarrier.arrive{.expect_tx}.shared::cta.b64 _, [r]{, tx}`, count 1, release, CTA scope:
  `some n` for the immediate transaction count `n`, `none` for a register. -/
  | arrive (tx : Option Int)
  /-- `mbarrier.try_wait.parity.shared::cta.b64` with a register parity, acquire, CTA scope. -/
  | wait
  /-- `tcgen05.commit.cta_group::1` without a multicast mask. -/
  | commit
  /-- A tensor load of mode `mode` to a CTA address without multicast. -/
  | issue (mode : TensorMode)
  deriving DecidableEq, Repr

/-- Whether operation `op` has shape `s`. -/
def Shape.ok : Shape → Op → Bool
  | .init, .mbarInit _ _ (.reg _) => true
  | .arrive tx, .mbarArrive _ _ t c cl rel sc st =>
    (match tx, t with
      | some n, .imm m => n == m
      | none, .reg _ => true
      | _, _ => false) && c == .imm 1 && !cl && rel && sc == .cta && st.isNone
  | .wait, .mbarWait _ _ _ (.reg _) acq sc => acq && sc == .cta
  | .commit, .tcCommit g _ _ mk => g == .one && mk.isNone
  | .issue md, .cpTensor _ grp _ _ _ _ _ _ mc md' _ => !grp && mc.isNone && md' == md
  | _, _ => false

/-- **The mbarrier sites of `[lo, hi)` are exactly `sites`**: every instruction there that
`mbarOp` selects is unguarded and listed with its shape, and every listed site lies in the
range and is such an instruction. -/
def regionOk (code : List Instr) (lo hi : Nat) (sites : List (Nat × Shape)) : Bool :=
  code.zipIdx.all (fun x => !(lo ≤ x.2 && x.2 < hi && mbarOp x.1.op) ||
      (x.1.guard.isNone && (sites.lookup x.2).any (fun s => s.ok x.1.op))) &&
    sites.all (fun s => lo ≤ s.1 && s.1 < hi &&
      (code[s.1]?).any (fun i => mbarOp i.op && s.2.ok i.op))

end MbarRow

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
