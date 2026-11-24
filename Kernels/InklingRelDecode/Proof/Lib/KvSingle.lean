-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingKvSlot
public import Lemmas.Protocol.SingleTmaRing.Items
public import Lemmas.Protocol.SingleTmaRing.Faults
public import Lemmas.Protocol.SingleTmaRing.RingFacts
public import Lemmas.Protocol.SingleTmaRing.Order
public import Lemmas.Protocol.SingleTmaRing.Poll
public import Lemmas.Protocol.SingleTmaRing.Attribution

@[expose] public section

/-! # The KV ring's slot as a slot of the library's single-CTA ring

A KV slot (`Kv.Slot`) is the library's `SingleTmaRing.Slot` with eight copies of 8192 bytes
(`Slot.toS`), and its hypotheses (`Kv.Hyp`) give the library's `SingleTmaRing.Hyp` at CTA scope
(`Hyp.toS`), constructor by constructor. The derived definitions of the KV ring (`opF`, `itF`,
`wE`, `wF`, `cmE`, `note`, `SF`, `SE`, `phF`, `phE`, `oF`, `oE`, `copyUse`, `readUse`) are the
library's at `S.toS` up to unfolding, so a theorem of the library applied to `H.toS` and
`Slot.fits` proves the KV statement with `exact`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Kv
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section
set_option maxRecDepth 100000

/-- The slot as a slot of the library's single-CTA ring: eight copies of 8192 bytes. -/
def Slot.toS (S : Slot) : SingleTmaRing.Slot :=
  ⟨S.full, S.empty, S.ap, S.cp, S.cm, 8, 8192, S.δ, S.pArr, S.pCp⟩

/-- The slot's use fits the barrier's transaction counter. -/
theorem Slot.fits (S : Slot) : S.toS.Fits := by
  show 0 < 8 ∧ 0 < 8192 ∧ 2 * (8 * 8192) ≤ MBarrier.limit
  unfold MBarrier.limit
  decide +kernel

theorem FullSource.toS {X : Execution} {S : Slot} {r : Record Ref} (h : FullSource X S r) :
    SingleTmaRing.FullSource X S.toS r := by
  cases h with
  | init ha => exact .init ha
  | poll hid he ha => exact .poll hid he ha
  | arrive hid he ha hb => exact .arrive hid he ha hb
  | preArrive hδ hid he ha => exact .preArrive hδ hid he ha
  | copy hid he hm ha hb => exact .copy hid he hm ha hb
  | preCopy hδ hid he hm ha => exact .preCopy (i := _) hδ hid he hm ha

theorem EmptySource.toS {X : Execution} {S : Slot} {r : Record Ref} (h : EmptySource X S r) :
    SingleTmaRing.EmptySource X S.toS r := by
  cases h with
  | init ha => exact .init ha
  | poll hid he ha => exact .poll hid he ha
  | notify hid he hm htg ha hb => exact .notify hid he hm htg ha hb

/-- The library's hypotheses at CTA scope. -/
theorem Hyp.toS {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution} {S : Slot}
    (H : Hyp L K A X S) : SingleTmaRing.Hyp L K A X S.toS .cta where
  δ_le := H.δ_le
  full_src r hr := (H.full_src r hr).toS
  empty_src r hr := (H.empty_src r hr).toS
  full_init := H.full_init
  empty_init := H.empty_init
  full_noInval := H.full_noInval
  empty_noInval := H.empty_noInval
  full_parity := H.full_parity
  empty_parity := H.empty_parity
  spins := H.spins
  full_acq := H.full_acq
  empty_acq := H.empty_acq
  cta := H.cta
  issue := H.issue
  pre_cta := H.pre_cta
  pre_ne := H.pre_ne
  pre_inj := H.pre_inj

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {S : Slot}

/-! ### The items of the KV definitions -/

theorem kOwner_of_zero {k : Kind} (hk : k.val = 0) : kOwner k = 0 := by simp [kOwner, hk]

theorem prod_one : S.prod 1 = S.cp := by simp [Slot.prod]

theorem kPred_zero : kPred S ⟨0, by omega⟩ = arrivesOn S.full := by simp [kPred]

/-- The prologue's items are of use 0. -/
theorem opF_pre_zero (h : S.δ = 1) : opF X S ⟨0, by omega⟩ 0 = S.pArr := by
  simp [opF, h]

theorem opF_pre_ne {k : Kind} (hk : k.val ≠ 0) (h : S.δ = 1) :
    opF X S k 0 = S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩ := by
  simp [opF, h, hk]

/-- The loader's items. -/
theorem opF_ld {k : Kind} {u : Nat} (h : ¬ (S.δ = 1 ∧ u = 0)) :
    opF X S k u = (S.prod (kOwner k), nthEv X (kPred S k) (S.prod (kOwner k))
      (kIdx k (u - S.δ))) := by
  simp [opF, h]

/-! ### The sources of the records and the counted items (`SingleTmaRing/Items`) -/

/-- An arrival on the full barrier is the loader's lane-0 arrival or the prologue's. -/
theorem arrival_source (H : Hyp L K A X S) {r : Record Ref} (hr : r ∈ X.objects S.full)
    {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = txBytes ∧
      ((∃ j pc rel sc, r.id = .thread (S.ap, j) ∧
        X.get (S.ap, j) = some ⟨pc, .arrive S.full txBytes 1 rel sc⟩ ∧
        arrivals S.full ((X.tr S.ap).take j) + 1 ≤ okPolls S.empty ((X.tr S.ap).take j)) ∨
      (S.δ = 1 ∧ r.id = .thread S.pArr ∧
        ∃ pc rel sc, X.get S.pArr = some ⟨pc, .arrive S.full txBytes 1 rel sc⟩)) :=
  SingleTmaRing.arrival_source H.toS hr ha

/-- A completion on the full barrier is a copy of the loader's elected lane, within its budget,
or one of the prologue's eight. -/
theorem completion_source (H : Hyp L K A X S) {r : Record Ref} (hr : r ∈ X.objects S.full)
    {n : Nat} (ha : r.action = .completeTx n) :
    n = copyBytes ∧
      ((∃ j pc al sp, r.id = .async (S.cp, j) (.notify .load) ∧
        X.get (S.cp, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
        ((X.tr S.cp).take j).countP (issuesTo S.full) + 1 ≤
          8 * okPolls S.empty ((X.tr S.cp).take j)) ∨
      (S.δ = 1 ∧ ∃ (i : Fin 8) (pc al : Nat) (sp : TensorCopy.Spec),
        r.id = .async (S.pCp i) (.notify .load) ∧
        X.get (S.pCp i) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full)) :=
  SingleTmaRing.completion_source H.toS hr ha

/-- A fault-free arrival or completion of the full barrier is a counted item. -/
theorem full_item (H : Hyp L K A X S) {r : Record Ref} (hr : r ∈ X.objects S.full)
    (hf : r.fault = none) (hu : (∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) :
    ∃ x ∈ SF X S, r.id = itF X S x.1 x.2 ∧ ((∃ n tx, r.action = .arrive n tx) ↔ x.1.val = 0) :=
  SingleTmaRing.full_item H.toS hr hf hu

/-- A fault-free arrival of the empty barrier is a counted notification. -/
theorem empty_item (H : Hyp L K A X S) {r : Record Ref} (hr : r ∈ X.objects S.empty)
    (hf : r.fault = none) {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ ∃ y ∈ SE X S, r.id = note X S y.1 0 y.2 :=
  SingleTmaRing.empty_item H.toS hr hf ha

/-- A counted copy item is the prologue's (use 0 of a preloaded slot), or the loader's elected
lane's, within its budget. -/
theorem item_completion (H : Hyp L K A X S) {x : Kind × Nat} (hk : x.1.val ≠ 0)
    {r : Record Ref} (hr : r ∈ X.objects S.full) (hid : r.id = itF X S x.1 x.2)
    (ha : r.action = .completeTx copyBytes) :
    (S.δ = 1 ∧ x.2 = 0 ∧ ∃ pc al sp, X.get (opF X S x.1 x.2) = some ⟨pc, .tensorIssue al sp⟩ ∧
      sp.mbar = S.full) ∨
    (¬ (S.δ = 1 ∧ x.2 = 0) ∧ ∃ j pc al sp, opF X S x.1 x.2 = (S.cp, j) ∧
      X.get (S.cp, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
      ((X.tr S.cp).take j).countP (issuesTo S.full) = 8 * (x.2 - S.δ) + (x.1.val - 1) ∧
      x.2 - S.δ + 1 ≤ okPolls S.empty ((X.tr S.cp).take j)) :=
  SingleTmaRing.item_completion H.toS hk hr hid ha

/-- The record of a counted item, and its event: the loader's event of its kind with the item's
count of earlier ones, after more successful polls of `empty` than the item's use less the
preloaded use; or the prologue's, for use 0 of a preloaded slot. -/
theorem SF_op (H : Hyp L K A X S) {x : Kind × Nat} (hx : x ∈ SF X S) :
    (∃ (i : Nat) (r : Record Ref), (X.objects S.full)[i]? = some r ∧ r.id = itF X S x.1 x.2 ∧
      r.fault = none ∧ (x.1.val = 0 → r.action = .arrive 1 txBytes) ∧
      (x.1.val ≠ 0 → r.action = .completeTx copyBytes)) ∧
    (∃ e, X.get (opF X S x.1 x.2) = some e) ∧
    (S.δ = 1 ∧ x.2 = 0 ∨ ∃ j, opF X S x.1 x.2 = (S.prod (kOwner x.1), j) ∧
      x.2 - S.δ + 1 ≤ okPolls S.empty ((X.tr (S.prod (kOwner x.1))).take j)) :=
  SingleTmaRing.SF_op H.toS hx

/-- The kind predicate holds of the item's event. -/
theorem SF_pred (H : Hyp L K A X S) {x : Kind × Nat} (hx : x ∈ SF X S) {e : Event}
    (he : X.get (opF X S x.1 x.2) = some e) : kPred S x.1 e = true :=
  SingleTmaRing.SF_pred H.toS hx he

/-! ### Attribution of the records (`SingleTmaRing/Attribution`) -/

/-- The record of a counted notification, and its consumer's commit: the commit with the use's
count of earlier ones, after more successful full polls of the consumer than the use. -/
theorem SE_op (H : Hyp L K A X S) {y : Fin 1 × Nat} (hy : y ∈ SE X S) :
    (∃ (i : Nat) (r : Record Ref), (X.objects S.empty)[i]? = some r ∧
      r.id = note X S y.1 0 y.2 ∧ r.fault = none ∧ r.action = .arrive 1 0) ∧
    (∃ pc sp, X.get (cmE X S y.1 y.2) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = S.empty ∧
      TcCommit.target sp rank0 = some S.empty ∧
      ((X.tr S.cm).take (cmE X S y.1 y.2).2).countP (commitsTo S.empty) = y.2) ∧
    y.2 + 1 ≤ okPolls S.full ((X.tr S.cm).take (cmE X S y.1 y.2).2) :=
  SingleTmaRing.SE_op H.toS hy

/-- A guard of the loader's items: the item of use `u ≥ 1` follows the producer's polls for the
uses `1, …, u`. -/
theorem guardP (H : Hyp L K A X S) {x : Kind × Nat} (hx : x ∈ SF X S) {n : Nat} (h1 : 1 ≤ n)
    (hn : n ≤ x.2) :
    Resumes K X (wE X S (kOwner x.1) n) (opF X S x.1 x.2) :=
  SingleTmaRing.guardP H.toS hx h1 hn

theorem guardM (H : Hyp L K A X S) {y : Fin 1 × Nat} (hy : y ∈ SE X S) {j : Nat} (hj : j ≤ y.2) :
    Resumes K X (wF X S y.1 j) (cmE X S y.1 y.2) :=
  SingleTmaRing.guardM H.toS hy hj

theorem issueF (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {x : Kind × Nat}
    (hx : x ∈ SF X S) :
    Relation.ReflTransGen (DepStep L K X) (.thread (opF X S x.1 x.2), false)
      (itF X S x.1 x.2, false) :=
  SingleTmaRing.issueF hX H.toS hx

theorem issueE (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {y : Fin 1 × Nat}
    (hy : y ∈ SE X S) :
    Relation.ReflTransGen (DepStep L K X) (.thread (cmE X S y.1 y.2), false)
      (note X S y.1 0 y.2, false) :=
  SingleTmaRing.issueE hX H.toS hy

/-- The full barrier has no pending-count increment. -/
theorem full_noIncrement (H : Hyp L K A X S) :
    incrementsBefore (X.objects S.full) (X.objects S.full).length = 0 :=
  SingleTmaRing.full_noIncrement H.toS

/-- Every non-faulting arrival of the full barrier is a unit arrival of a counted item of kind
`0`. -/
theorem full_count (H : Hyp L K A X S) : ∀ (k : Nat) (r : MBarrier.Record Ref) (n tx : Nat),
      (X.objects S.full)[k]? = some r → r.fault = none → r.action = .arrive n tx →
      n = 1 ∧ ∃ x ∈ (SF X S).filter (fun x => x.1 ∈ ({⟨0, by omega⟩} : Finset Kind)),
        r.id = itF X S x.1 x.2 :=
  SingleTmaRing.full_count H.toS

/-- **The consumer's poll for use `j`** found phase `j + 1` of the full barrier and observed
phase `j`. -/
theorem F_found (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin 1} {j : Nat}
    (hj : j < okPolls S.full (X.tr S.cm)) :
    ∃ i w st, (X.objects S.full)[i]? = some w ∧
      w.id = .thread (wF X S b j) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects S.full) i = some st ∧ st.phase = j + 1 ∧
      observedAt (X.objects S.full) i = some j ∧ oF X S b j = j :=
  SingleTmaRing.F_found (b := b) hX H.toS S.fits hj

/-- **The items of use `j`.** The consumer's poll for use `j` observed every item of use `j`. -/
theorem consumer_observes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin 1} {j : Nat}
    (hj : j < okPolls S.full (X.tr S.cm)) (k : Kind) :
    (k, j) ∈ SF X S ∧ phF X S (k, j) = j ∧
      UpdateBeforeWait (X.objects S.full) (itF X S k j) (.thread (wF X S b j)) :=
  SingleTmaRing.consumer_observes (b := b) hX H.toS S.fits hj k

/-- **The notifications of use `n`.** Producer `a`'s poll for use `n + 1` observed the consumer's
notification of use `n`. -/
theorem producer_observes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n : Nat}
    (hj : n + 1 - S.δ < okPolls S.empty (X.tr (S.prod a))) (b : Fin 1) :
    (b, n) ∈ SE X S ∧ phE X S (b, n) = n ∧
      UpdateBeforeWait (X.objects S.empty) (note X S b a n) (.thread (wE X S a (n + 1))) :=
  SingleTmaRing.producer_observes hX H.toS S.fits hj b

/-- **Slot `S` as a ring of items.** -/
def ring (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) :
    MbarRing.Items.Ring L K A X 2 1 1 (fun _ => 9) where
  owner _ := 0
  ownF _ k := kOwner k
  wE := wE X S
  opF _ := opF X S
  itF _ := itF X S
  wF := wF X S
  cm := cmE X S
  note := note X S
  SF _ := SF X S
  phF _ := phF X S
  SE _ := SE X S
  phE _ := phE X S
  oF := oF X S
  oE := oE X S
  cover := (SingleTmaRing.ring hX H.toS S.fits).cover
  guardP := (SingleTmaRing.ring hX H.toS S.fits).guardP
  issueF := (SingleTmaRing.ring hX H.toS S.fits).issueF
  guardM := (SingleTmaRing.ring hX H.toS S.fits).guardM
  issue := (SingleTmaRing.ring hX H.toS S.fits).issue
  obsF := (SingleTmaRing.ring hX H.toS S.fits).obsF
  obsE := (SingleTmaRing.ring hX H.toS S.fits).obsE
  fullF := (SingleTmaRing.ring hX H.toS S.fits).fullF
  fullE := (SingleTmaRing.ring hX H.toS S.fits).fullE
  ltF := (SingleTmaRing.ring hX H.toS S.fits).ltF
  ltE := (SingleTmaRing.ring hX H.toS S.fits).ltE

/-! ### Uses and transactions (`SingleTmaRing/RingFacts`) -/

theorem okPolls_take_le (m : Loc) (es : List Event) (k : Nat) :
    Flow.okPolls m (es.take k) ≤ Flow.okPolls m es :=
  SingleTmaRing.okPolls_take_le m es k

/-- A counted item's use is at most the phase of the full barrier before its record. -/
theorem use_le_phase (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {x : Kind × Nat}
    (hx : x ∈ SF X S) {i : Nat} {r : Record Ref} (hi : (X.objects S.full)[i]? = some r)
    (hid : r.id = itF X S x.1 x.2) {st : State}
    (hst : stateBefore (X.objects S.full) i = some st) : x.2 ≤ st.phase :=
  SingleTmaRing.use_le_phase hX H.toS S.fits hx hi hid hst

/-- The full barrier's transaction count stays within one use's bytes either side of zero. -/
theorem full_tx_bounds (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {j : Nat}
    (hj : j ≤ (X.objects S.full).length) {st : State}
    (hst : stateBefore (X.objects S.full) j = some st) :
    -(txBytes : Int) ≤ st.tx ∧ st.tx ≤ txBytes :=
  SingleTmaRing.full_tx_bounds hX H.toS S.fits hj hst

/-- The empty barrier's transaction count is zero. -/
theorem empty_tx_zero (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {j : Nat}
    (hj : j ≤ (X.objects S.empty).length) {st : State}
    (hst : stateBefore (X.objects S.empty) j = some st) : st.tx = 0 :=
  SingleTmaRing.empty_tx_zero hX H.toS hj hst

/-! ### The order of the slot's copies and the MMA lane's reads (`SingleTmaRing/Order`) -/

open Classical in
/-- The use of the slot a copy issue is for: 0 for the prologue's copies, else the loader's earlier
copies on `full` over eight, plus the preloaded use. -/
def copyUse (X : Execution) (S : Slot) (e : EvId) : Nat :=
  if S.δ = 1 ∧ ∃ i : Fin 8, e = S.pCp i then 0
  else ((X.tr e.1).take e.2).countP (issuesTo S.full) / 8 + S.δ

/-- The use of the slot a read of the MMA lane is in: its earlier commits to `empty`. -/
def readUse (X : Execution) (S : Slot) (e : EvId) : Nat :=
  ((X.tr e.1).take e.2).countP (commitsTo S.empty)

/-- A tensor-core MMA or copy issue is not a commit. -/
theorem commits_tcAsync_succ {g k : Nat} {m : Loc} (h : X.TcAsync (g, k)) :
    ((X.tr g).take (k + 1)).countP (commitsTo m) = ((X.tr g).take k).countP (commitsTo m) :=
  SingleTmaRing.commits_tcAsync_succ h

theorem tcAsync_lt {g k : Nat} (h : X.TcAsync (g, k)) : k < (X.tr g).length :=
  SingleTmaRing.tcAsync_lt h

/-- Threads of one CTA meet at every scope. -/
theorem scopesMeet {g h : Nat} (hs : SameCta L g h) (us ws : MbarScope) :
    ScopesMeet L us g ws h :=
  SingleTmaRing.scopesMeet hs us ws

section Order
variable (hX : Consistent L K A mem0 X)
include hX

/-- **A copy is observed by its use's poll.** The consumer's successful full poll with `u` earlier
ones observes the completion of a copy issue on the full barrier of use `u`. -/
theorem copy_observed (H : Hyp L K A X S) {gl kl pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (gl, kl) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full) {j pcw p : Nat}
    {acq : Bool} {sc : MbarScope} (hew : X.get (S.cm, j) = some ⟨pcw, .wait S.full p true acq sc⟩)
    (hj : okPolls S.full ((X.tr S.cm).take j) = copyUse X S (gl, kl)) :
    AsyncObserved X (gl, kl) (.notify .load) (S.cm, j) true sc :=
  SingleTmaRing.copy_observed hX S.fits H.toS he hm hew hj

/-- **A copy before a read.** A copy on the full barrier of use `u` is ordered before a read of the
MMA lane, at a byte both cover, that has polled the full barrier successfully more than `u` times
before it. -/
theorem copy_before_read (H : Hyp L K A X S) {km : Nat} (hkm : km < (X.tr S.cm).length)
    {gl kl pcl al : Nat} {spl : TensorCopy.Spec}
    (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩) (hml : spl.mbar = S.full)
    (hpolls : copyUse X S (gl, kl) + 1 ≤ okPolls S.full ((X.tr S.cm).take km)) {x y z : Nat}
    {l : Loc} {isB : Bool} {idx : Nat} (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (S.cm, km) (.mmaRead isB idx) l) :
    AsyncBefore L X l ((gl, kl), .write (.load x y z)) ((S.cm, km), .mmaRead isB idx) :=
  SingleTmaRing.copy_before_read hX S.fits H.toS hkm hel hml hpolls hca hcb

/-- **A producer's poll acquires an earlier read.** A read of the MMA lane, with at most `q`
commits of the lane to the slot up to it, is acquired by a successful empty poll of producer `a`
at or before its successful poll with `q + 1 - δ` earlier ones (the poll for use `q + 1`). -/
theorem read_observed (H : Hyp L K A X S) {a : Fin 2} {km : Nat} (hR : X.TcAsync (S.cm, km))
    {jl pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hwl : X.get (S.prod a, jl) = some ⟨pc, .wait S.empty p true acq sc⟩) {q : Nat}
    (hq : okPolls S.empty ((X.tr (S.prod a)).take jl) + S.δ = q + 1)
    (hK : ((X.tr S.cm).take (km + 1)).countP (commitsTo S.empty) ≤ q) :
    ∃ jw, jw ≤ jl ∧ AsyncObserved X (S.cm, km) .mmaDone (S.prod a, jw) true .cta :=
  SingleTmaRing.read_observed hX S.fits H.toS hR hwl hq hK

/-- **A read before a copy.** A read of the MMA lane is ordered before a copy of the loader's
elected lane, at a byte both cover, when the lane's commits to the slot up to the read are fewer
than the copy's use; and a wait observes the read's completion. -/
theorem read_before_copy (H : Hyp L K A X S) {km : Nat} (hR : X.TcAsync (S.cm, km))
    {kl pcl al : Nat} {spl : TensorCopy.Spec}
    (hel : X.get (S.cp, kl) = some ⟨pcl, .tensorIssue al spl⟩) (hml : spl.mbar = S.full)
    (hcnt : ((X.tr S.cm).take (km + 1)).countP (commitsTo S.empty) + 1 ≤ copyUse X S (S.cp, kl))
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (S.cm, km) (.mmaRead isB idx) l)
    (hcb : AsyncCovers X (S.cp, kl) (.write (.load x y z)) l) :
    AsyncBefore L X l ((S.cm, km), .mmaRead isB idx) ((S.cp, kl), .write (.load x y z)) ∧
      ∃ w ws, AsyncObserved X (S.cm, km) .mmaDone w true ws :=
  SingleTmaRing.read_before_copy hX S.fits H.toS hR hel hml hcnt hca hcb

/-- **A copy and a read of one byte are ordered by their uses.** A copy on the full barrier and a
read of the MMA lane that has polled the full barrier successfully more times than its earlier
commits to the slot, at a byte both cover: the copy is before the read when the copy's use is at
most the read's (RAW, `kv_ready`), the read is before the copy when its use is below the copy's
(WAR, `kv_empty`). -/
theorem copy_read_order (H : Hyp L K A X S) {km : Nat} (hR : X.TcAsync (S.cm, km))
    (hcR : readUse X S (S.cm, km) + 1 ≤ okPolls S.full ((X.tr S.cm).take km)) {gl kl pcl al : Nat}
    {spl : TensorCopy.Spec} (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩)
    (hml : spl.mbar = S.full) {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (S.cm, km) (.mmaRead isB idx) l) :
    (copyUse X S (gl, kl) ≤ readUse X S (S.cm, km) →
      AsyncBefore L X l ((gl, kl), .write (.load x y z)) ((S.cm, km), .mmaRead isB idx)) ∧
    (readUse X S (S.cm, km) < copyUse X S (gl, kl) →
      AsyncBefore L X l ((S.cm, km), .mmaRead isB idx) ((gl, kl), .write (.load x y z))) :=
  SingleTmaRing.copy_read_order hX S.fits H.toS hR hcR hel hml hca hcb

/-- **Any lane's successful poll of `full`.** -/
theorem lane_poll_full (H : Hyp L K A X S) {g k pc p : Nat}
    {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait S.full p true acq sc⟩) :
    ∃ i w st, (X.objects S.full)[i]? = some w ∧ w.id = .thread (g, k) ∧
      stateBefore (X.objects S.full) i = some st ∧
      okPolls S.full ((X.tr g).take k) + 1 ≤ st.phase ∧ Open p st.phase :=
  SingleTmaRing.lane_poll_full hX H.toS he

end Order

/-! ### Fault freedom (`SingleTmaRing/Faults`) -/

/-- **Every record of the ring slot's barriers is fault-free.** -/
theorem fault_free (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {m : Loc}
    (hm : m = S.full ∨ m = S.empty) {r : Record Ref} (hr : r ∈ X.objects m) :
    r.fault = none :=
  SingleTmaRing.fault_free hX H.toS S.fits hm hr

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Kv
