-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOEpi
public import Lemmas.Protocol.UnitNotify
public import Lemmas.Protocol.ObservedSync
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-!
# The objects of the S/P/O handshake, from the record sources

The hypothesis structure of one CTA's handshake barriers, in the form of `Kv.Hyp` for the KV
ring (`Ring.lean`) and of FA4's `SFullFacts`/`PReadyFacts`/`TmemFacts`. One CTA `c`; the
committing thread `cm` (the MMA warp's elected lane) and the arriving thread `p0` (thread 0 of
the default partition).

* **`CommitBar`**: `s_ready b`, `o_done`, `o_final`: completed by the notifications of the commits
  of `cm` and nothing else. They are commit objects (`MbarRing.Notify.Obj`) of `cm`: `sObj`,
  `fObj`.
* **`pReady`**: `p_ready b`: completed by the unit arrivals of `p0` and nothing else: a unit object
  (`MbarRing.Unit.Obj`, one producer, offset 0): `pObj`.
* `Facts`: the record sources of the six objects (who touches them), the initialization, and the
  parity of the polls. The sources are the classification of every event of the kernel that names
  one of the objects; the parities are the execution-level theorems of `SOMmaExec`, `SOSmExec`,
  `SOEpi` once the role-table protocol gives each polling thread's run. The kernel-wide negative
  facts (no bulk copy, no `cp.async.mbarrier.arrive`, no cancellation request, no invalidation) are
  `TmemFacts`'s of FA4.
* **`o_done` is a commit object of the same kind** (`SOOdone.oObj`): the fixed kernel polls it in
  every iteration from the second, so a thread's earlier polls alternate and `commitObj` applies
  with the parity `SOOdone.o_parity_of_runs`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section

/-- A barrier completed by commits: `s_ready b`, `o_done`, `o_final` of CTA `c`. -/
def CommitBar (L : Launch) (c : Nat) (m : Loc) : Prop :=
  (∃ b, b < 2 ∧ m = sReady L c b) ∨ m = oDone L c ∨ m = oFinal L c

/-- A barrier completed by thread arrivals: `p_ready b` of CTA `c`. -/
def PBar (L : Launch) (c : Nat) (m : Loc) : Prop := ∃ b, b < 2 ∧ m = pReady L c b

/-- **The thread-layer facts of CTA `c`'s handshake barriers.** -/
structure Facts (L : Launch) (X : Execution) (c cm p0 : Nat) : Prop where
  /-- The kernel has no linear copy, cancellation request, barrier invalidation, or
  `cp.async.mbarrier.arrive`. -/
  no_bulk : ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩
  no_clc : ∀ {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat},
    X.get i ≠ some ⟨pc, .clcIssue sp tg⟩
  no_inval : ∀ {i : EvId} {pc : Nat} {m : Loc}, X.get i ≠ some ⟨pc, .mbInval m⟩
  no_arriveOn : ∀ {i : EvId} {pc : Nat} {m : Loc} {noinc : Bool},
    X.get i ≠ some ⟨pc, .asyncArrive m noinc⟩
  /-- No tensor copy completes on a handshake barrier (the copies complete on `kv_ready`). -/
  no_tensor : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → ¬ CommitBar L c sp.mbar ∧ ¬ PBar L c sp.mbar
  /-- A commit notifying `s_ready b`, `o_done` or `o_final` of the CTA is `cm`'s and names the
  barrier itself (single-CTA commits). -/
  commit_only : ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc},
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m → CommitBar L c m →
      i.1 = cm ∧ sp.mbar = m
  /-- No commit notifies `p_ready`. -/
  no_commit_p : ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc},
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m → ¬ PBar L c m
  /-- No thread arrives on a commit barrier. -/
  no_arrive_commit : ∀ {g i pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope},
    CommitBar L c m → X.get (g, i) ≠ some ⟨pc, .arrive m tx cnt rel sc⟩
  /-- An arrival on `p_ready` is `p0`'s: one unit without transaction bytes, a release. -/
  p_arrive : ∀ {g i pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope},
    PBar L c m → X.get (g, i) = some ⟨pc, .arrive m tx cnt rel sc⟩ →
      g = p0 ∧ tx = 0 ∧ cnt = 1 ∧ rel = true
  /-- Every handshake barrier is initialized first with count 1 and never invalidated
  (obligation 1). -/
  init : ∀ {m : Loc}, CommitBar L c m ∨ PBar L c m → PairTmaRing.InitFirst X m 1
  /-- A successful poll of `s_ready b` has the parity of the thread's earlier ones
  (`SOSmExec.sm_swait_exec`: `n % 2`, offset 0). -/
  s_parity : ∀ {g k pc p b : Nat} {acq : Bool} {sc : MbarScope}, b < 2 →
    X.get (g, k) = some ⟨pc, .wait (sReady L c b) p true acq sc⟩ →
      p % 2 = (okPolls (sReady L c b) ((X.tr g).take k) + 0) % 2
  /-- A successful poll of `p_ready b` has the parity of the thread's earlier ones
  (`SOMmaExec.mma_pwait_exec`). -/
  p_parity : ∀ {g k pc p b : Nat} {acq : Bool} {sc : MbarScope}, b < 2 →
    X.get (g, k) = some ⟨pc, .wait (pReady L c b) p true acq sc⟩ →
      p % 2 = (okPolls (pReady L c b) ((X.tr g).take k) + 0) % 2
  /-- A successful poll of `o_final` has the parity of the thread's earlier ones
  (`SOEpi.epi_fwait`: parity 0 with none before). -/
  f_parity : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (oFinal L c) p true acq sc⟩ →
      p % 2 = (okPolls (oFinal L c) ((X.tr g).take k) + 0) % 2

variable {L : Launch} {X : Execution} {c cm p0 : Nat} {K : Kernel} {A : List Assumption}
  {mem0 : Mem0}

theorem CommitBar.sReady {b : Nat} (hb : b < 2) : CommitBar L c (sReady L c b) := .inl ⟨b, hb, rfl⟩
theorem CommitBar.oFinal : CommitBar L c (oFinal L c) := .inr (.inr rfl)

/-- **A commit barrier is a commit object of `cm`.** -/
theorem commitObj (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0) {m : Loc}
    (hm : CommitBar L c m)
    (hpar : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
        p % 2 = (okPolls m ((X.tr g).take k) + 0) % 2) :
    MbarRing.Notify.Obj X m cm m 0 :=
  MbarRing.Notify.Obj.of_commits hX (F.init (.inl hm)) (fun he => F.no_arrive_commit hm he)
    (fun he hmbar => (F.no_tensor he).1 (hmbar ▸ hm))
    (fun he => (F.no_bulk he).elim) (fun he => (F.no_arriveOn he).elim) F.no_clc F.no_inval
    (fun he ht => F.commit_only he ht hm) hpar (Nat.zero_le _)

/-- **`s_ready b` is a commit object of `cm`.** -/
theorem sObj (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0) {b : Nat} (hb : b < 2) :
    MbarRing.Notify.Obj X (sReady L c b) cm (sReady L c b) 0 :=
  commitObj hX F (CommitBar.sReady hb) (fun he => F.s_parity hb he)

/-- **`o_final` is a commit object of `cm`.** -/
theorem fObj (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0) :
    MbarRing.Notify.Obj X (oFinal L c) cm (oFinal L c) 0 :=
  commitObj hX F CommitBar.oFinal F.f_parity

/-- **`p_ready b` is a unit object of `p0`**: one producer, offset 0. -/
theorem pObj (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0) {b : Nat} (hb : b < 2) :
    MbarRing.Unit.Obj X (pReady L c b) 1 (fun _ => p0) 0 where
  pos := by decide
  inj := fun _ _ _ => Subsingleton.elim _ _
  src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (F.no_inval he).elim
    | @arrive g j pc tx cnt rel sc hid he ha =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := F.p_arrive ⟨b, hb, rfl⟩ he
      exact .arrive hid ⟨0, rfl⟩ he ha
    | wait hid he ha => exact .poll hid he ha
    | tensor _ he hm _ => exact ((F.no_tensor he).2 (hm ▸ ⟨b, hb, rfl⟩)).elim
    | increment _ he _ => exact (F.no_arriveOn he).elim
    | arriveOn _ he _ _ _ => exact (F.no_arriveOn he).elim
    | bulk _ he _ _ _ => exact (F.no_bulk he).elim
    | commit _ he htg _ => exact (F.no_commit_p he htg ⟨b, hb, rfl⟩).elim
    | clc _ he _ _ _ => exact (F.no_clc he).elim
  init := F.init (.inr ⟨b, hb, rfl⟩)
  noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => F.no_inval he) _
  parity he := F.p_parity hb he
  δ_le := Nat.zero_le _

end
end PTX.Kernels.InklingRelDecode.Proof.SO
