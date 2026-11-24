-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Protocol.PairTmaRing.Decl
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Flow.ElectActor
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # A slot of the Q or KV ring as a pair TMA ring slot

The Q ring's stages and the KV ring's slots share one shape: a full barrier `b` (`FBar.isFull`)
of the pair's even CTA `2 c`, its partner empty barrier in each CTA `2 c + a`, the elected lane
of each CTA's loader as producer, the elected lane of the even CTA's MMA warp as the one
consumer, `b.copies` copies of `b.copyBytes` bytes per CTA and use. `slot L X c b` is that
`PairTmaRing.Slot` (this file serves both rings: `QRing` and `KvRing` instantiate it).

The producers and the consumer are the lead threads of their warps (`leadOf`): the thread of
the warp whose full-mask election returned its lane (`LeadAt`). Two such threads of one warp
are one (`leadOf_eq`, by the determinism of elections), so every arrival, copy and commit the
thread layer attributes to an elected lane is the slot's producer's or consumer's.

Both rings are declared as data (`decl`, `PairTmaRing.Decl`: the Q ring `qDecl` with two
stages, the KV ring `kvDecl` with six slots). Their thread-side events (`events`,
`PairTmaRing.Decl.Events`) follow from the ring facts (`RingFacts`), the absence of bulk copies,
cancellation requests and invalidations (`TmemFacts`) and one premise:

* **`RingInit`**: every ring barrier's history starts with its initialization (count 1), its
  only one. It follows from the initialization's publication by `fence.mbarrier_init` and the
  start cluster barrier (OBJ-MBAR-INIT-PUBLICATION); the table-wide proof is `InitFirst`'s.

The hypotheses of every slot follow from the declaration and its events by the library
(`PairTmaRing.Decl.hyp`, `hyp`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace Rings

/-! ### The ring barriers -/

theorem isFull_ring {b : FBar} (h : b.isFull) : b.ring := by
  cases b <;> simp_all [FBar.isFull, FBar.ring]

theorem partner_ring {b : FBar} (h : b.isFull) : b.partner.ring := by
  cases b <;> simp_all [FBar.isFull, FBar.ring, FBar.partner]

theorem not_isEmpty {b : FBar} (h : b.isFull) : b.isEmpty = false := by
  cases b <;> simp_all [FBar.isFull, FBar.isEmpty]

theorem partner_not_isFull {b : FBar} (h : b.isFull) : b.partner.isFull = false := by
  cases b <;> simp_all [FBar.isFull, FBar.partner]

theorem partner_partner {b : FBar} (h : b.isFull) : b.partner.partner = b := by
  cases b <;> simp_all [FBar.isFull, FBar.partner]

theorem pollOffset_full {b : FBar} (h : b.isFull) : b.pollOffset = 0 := by
  cases b <;> simp_all [FBar.isFull, FBar.pollOffset]

theorem pollOffset_partner {b : FBar} (h : b.isFull) : b.partner.pollOffset = 1 := by
  cases b <;> simp_all [FBar.isFull, FBar.pollOffset, FBar.partner]

theorem copies_pos {b : FBar} (h : b.isFull) : 0 < b.copies := by
  cases b <;> simp_all [FBar.isFull, FBar.copies]
  split_ifs <;> omega

theorem copyBytes_pos {b : FBar} (h : b.isFull) : 0 < b.copyBytes := by
  cases b <;> simp_all [FBar.isFull, FBar.copyBytes]
  split_ifs <;> omega

theorem useBytes_le {b : FBar} (h : b.isFull) : 2 * b.useBytes ≤ MBarrier.limit := by
  cases b <;> simp_all [FBar.isFull, FBar.useBytes, FBar.copies, FBar.copyBytes,
    MBarrier.limit]

/-! ### The lead threads -/

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

open Classical in
/-- The lead thread of warp `w` of CTA `cta`: the thread of the warp an election returned the
lane of, when there is one (else its lane 0). -/
def leadOf (L : Launch) (X : Execution) (cta w : Nat) : Nat :=
  if h : ∃ g, g < L.threads ∧ ctaOf L g = cta ∧ warpOf L g = w ∧ ∃ k, LeadAt L X g k then
    h.choose
  else cta * L.block + 32 * w

/-- Two elected threads of one warp are one thread. -/
theorem lead_unique (hX : Consistent L kernel asms mem0 X) {g h k k' : Nat}
    (hg : g < L.threads) (hh : h < L.threads) (hc : ctaOf L g = ctaOf L h)
    (hw : warpOf L g = warpOf L h) (hlg : LeadAt L X g k) (hlh : LeadAt L X h k') : g = h := by
  obtain ⟨j, -, pc, inst, he⟩ := hlg
  obtain ⟨j', -, pc', inst', he'⟩ := hlh
  exact selected_elect_thread_unique hX.elect he he' ⟨⟨hg, hh, hc⟩, hw⟩ rfl rfl

/-- **An elected thread is its warp's lead thread.** -/
theorem leadOf_eq (hX : Consistent L kernel asms mem0 X) {g k : Nat} (hg : g < L.threads)
    (hl : LeadAt L X g k) : leadOf L X (ctaOf L g) (warpOf L g) = g := by
  have hex : ∃ g', g' < L.threads ∧ ctaOf L g' = ctaOf L g ∧ warpOf L g' = warpOf L g ∧
      ∃ k, LeadAt L X g' k := ⟨g, hg, rfl, rfl, k, hl⟩
  simp only [leadOf, hex, dite_true]
  obtain ⟨h1, h2, h3, k', h4⟩ := hex.choose_spec
  exact lead_unique hX h1 hg h2 h3 h4 hl

/-- The lead thread of a warp of a CTA is in that CTA and warp. -/
theorem leadOf_place (hpre : Pre P L mem0) {cta w : Nat} (hw : w < 16) :
    ctaOf L (leadOf L X cta w) = cta ∧ warpOf L (leadOf L X cta w) = w := by
  unfold leadOf
  split
  · rename_i h
    obtain ⟨-, h2, h3, -⟩ := h.choose_spec
    exact ⟨h2, h3⟩
  · have hb := hpre.block
    unfold ctaOf warpOf
    rw [hb]
    constructor <;> omega

/-! ### The slot -/

/-- **Slot `b` of pair `c`** (`b` a full barrier of the Q or KV ring) as a pair TMA ring slot. -/
def slot (L : Launch) (X : Execution) (c : Nat) (b : FBar) : PairTmaRing.Slot 1 where
  full := b.loc L (2 * c)
  empty a := b.partner.loc L (2 * c + a.val)
  prod a := leadOf L X (2 * c + a.val) 14
  cons _ := leadOf L X (2 * c) 12
  n := b.copies
  bytes := b.copyBytes

/-- **The initialization premise**: the history of each ring barrier starts with its only
initialization, without fault, with the barrier's count. -/
def RingInit (L : Launch) (X : Execution) : Prop :=
  ∀ cta (b : FBar), b.ring → PairTmaRing.InitFirst X (b.loc L cta) 1

theorem ctaOf_lead (hpre : Pre P L mem0) {c : Nat} (a : Fin 2) :
    ctaOf L ((slot L X c b).prod a) = 2 * c + a.val :=
  (leadOf_place hpre (by decide)).1

theorem ctaOf_cons (hpre : Pre P L mem0) {c : Nat} (i : Fin 1) :
    ctaOf L ((slot L X c b).cons i) = 2 * c :=
  (leadOf_place hpre (by decide)).1

variable {b : FBar} {c : Nat}

/-- An arrival on the slot's full barrier is producer 0's, within its budget. -/
theorem full_arrive (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (hb : b.isFull) {g j pc tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .arrive (b.loc L (2 * c)) tx cnt rel sc⟩) :
    g = (slot L X c b).prod 0 ∧ tx = b.useBytes ∧ cnt = 1 ∧
      arrivals (b.loc L (2 * c)) ((X.tr g).take j) + 1 ≤
        okPolls (b.partner.loc L (2 * c)) ((X.tr g).take j) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hc, -, hw, hl, htx, hcnt, hbud⟩ := ht.arrive hg he (isFull_ring hb)
  have h := leadOf_eq hX hg hl
  rw [hw, ← hc] at h
  exact ⟨h.symm, htx, hcnt, hbud⟩

/-- A copy completing on the slot's full barrier is producer `a`'s, of the slot's copy bytes,
within its budget. -/
theorem full_issue (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (hb : b.isFull) {g k pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = b.loc L (2 * c)) :
    ∃ a : Fin 2, g = (slot L X c b).prod a ∧ ctaOf L g = 2 * c + a.val ∧
      TensorTransfer.bytes sp.descriptor = b.copyBytes ∧
      ((X.tr g).take k).countP (issuesTo (b.loc L (2 * c))) + 1 ≤
        b.copies * okPolls (b.partner.loc L (ctaOf L g)) ((X.tr g).take k) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hc, hw, hl, hby, hbud⟩ := ht.issue hg he hm (isFull_ring hb)
  unfold pairBase at hc
  have h := leadOf_eq hX hg hl
  rw [hw] at h
  refine ⟨⟨ctaOf L g % 2, Nat.mod_lt _ (by decide)⟩, ?_, by simp only; omega, hby, hbud⟩
  simp only [slot]
  rw [show 2 * c + ctaOf L g % 2 = ctaOf L g by omega, h]

/-- A commit notifying the slot's empty barrier of CTA `2 c + a` is the consumer's, at rank `a`,
to the leader's empty barrier, within its budget. -/
theorem empty_commit (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (hb : b.isFull) {a : Fin 2} {g j pc : Nat} {sp : TcCommit.Spec}
    {r : Fin 16} (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some (b.partner.loc L (2 * c + a.val))) :
    g = (slot L X c b).cons 0 ∧ r = PairTmaRing.rankOf a ∧ sp.mbar = b.partner.loc L (2 * c) ∧
      ((X.tr g).take j).countP (commitsTo sp.mbar) + 1 ≤
        okPolls (b.loc L (2 * c)) ((X.tr g).take j) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hw, hev, hl, hmb, hcb, hcs, hbud⟩ := ht.commit hg he htg (partner_ring hb)
  have ht' := htg
  simp only [TcCommit.target] at ht'
  split_ifs at ht' with hr
  simp only [Option.some.injEq, FBar.loc, Loc.mk.injEq, true_and] at ht'
  have hr1 := hr.1
  have hcta : ctaOf L g = 2 * c := by have := a.isLt; omega
  have hra : r = PairTmaRing.rankOf a := by
    apply Fin.ext; simp only [PairTmaRing.rankOf]; omega
  have h := leadOf_eq hX hg hl
  rw [hw, hcta] at h
  rw [partner_partner hb, hcta] at hbud
  rw [hcta] at hmb
  exact ⟨h.symm, hra, hmb, hbud⟩

/-! ### The rings as declared data -/

/-- **The ring of pair `c` whose slot `s` has full barrier `fullOf s`**, as a declared pair TMA
ring: the Q ring (`qDecl`, two stages) or the KV ring (`kvDecl`, six slots). Its slot `s` is
`slot L X c (fullOf s)`. -/
def decl (L : Launch) (X : Execution) (c : Nat) {n : Nat} (fullOf : Fin n → FBar) :
    PairTmaRing.Decl 1 where
  depth := n
  full s := (fullOf s).loc L (2 * c)
  empty s a := (fullOf s).partner.loc L (2 * c + a.val)
  prod a := leadOf L X (2 * c + a.val) 14
  cons _ := leadOf L X (2 * c) 12
  copies s := (fullOf s).copies
  bytes s := (fullOf s).copyBytes

/-- The Q ring of pair `c`: stage `st` has full barrier `qFull st`. -/
abbrev qDecl (L : Launch) (X : Execution) (c : Nat) : PairTmaRing.Decl 1 := decl L X c FBar.qFull

/-- The KV ring of pair `c`: slot `s` has full barrier `kvFull s`. -/
abbrev kvDecl (L : Launch) (X : Execution) (c : Nat) : PairTmaRing.Decl 1 :=
  decl L X c FBar.kvFull

/-- **The thread-side events of a ring of pair `c`**, from the ring facts (`RingFacts`), the
absence of linear copies, cancellation requests and invalidations (`TmemFacts`) and the
initialization premise (`RingInit`). -/
theorem events (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X)
    (htm : TmemFacts L X) (hinit : RingInit L X) {n : Nat} {fullOf : Fin n → FBar}
    (hf : ∀ s, (fullOf s).isFull) (c : Nat) : (decl L X c fullOf).Events L kernel asms X where
  copies_pos s := copies_pos (hf s)
  bytes_pos s := copyBytes_pos (hf s)
  nc_pos := Nat.one_pos
  tx_le s := useBytes_le (hf s)
  prod_inj a a' h := by
    have h1 := ctaOf_lead (X := X) (b := .kvFull 0) (c := c) hpre a
    have h2 := ctaOf_lead (X := X) (b := .kvFull 0) (c := c) hpre a'
    change leadOf L X (2 * c + a.val) 14 = leadOf L X (2 * c + a'.val) 14 at h
    simp only [slot] at h1 h2
    rw [h] at h1
    exact Fin.ext (by omega)
  cons_inj a a' _ := Subsingleton.elim a a'
  arrive s _ _ _ _ _ _ _ he := by
    obtain ⟨rfl, htx, rfl, hbud⟩ := full_arrive hX ht (hf s) he
    exact ⟨rfl, htx, rfl, hbud⟩
  arrive_empty s a _ _ _ _ _ _ _ he := by
    have := (ht.arrive (Frame.lt_of_get hX he) he (partner_ring (hf s))).1
    rw [partner_not_isFull (hf s)] at this
    cases this
  issue s _ _ _ _ _ he hm := by
    obtain ⟨a, rfl, hcta, hby, hbud⟩ := full_issue hX ht (hf s) he hm
    refine ⟨a, rfl, hby, ?_⟩
    rw [hcta] at hbud
    exact hbud
  issue_empty s a _ _ _ _ _ he hm := by
    have := (ht.issue (Frame.lt_of_get hX he) he hm (partner_ring (hf s))).1
    rw [partner_not_isFull (hf s)] at this
    cases this
  commit s a _ _ _ _ _ he htg := by
    obtain ⟨rfl, hr, hmb, hbud⟩ := empty_commit hX ht (hf s) he htg
    exact ⟨0, rfl, hr, hmb, hbud⟩
  commit_full s _ _ _ _ _ he htg := by
    have := (ht.commit (Frame.lt_of_get hX he) he htg (isFull_ring (hf s))).1
    rw [not_isEmpty (hf s)] at this
    cases this
  no_bulk := htm.no_bulk
  no_arriveOn := htm.no_arriveOn
  no_clc := htm.no_clc
  no_inval := htm.no_inval
  full_init s := hinit _ _ (isFull_ring (hf s))
  empty_init s a := hinit _ _ (partner_ring (hf s))
  full_parity s _ _ _ _ _ _ he := by
    have := (ht.poll (Frame.lt_of_get hX he) he (isFull_ring (hf s))).2.2.2.1
    rw [pollOffset_full (hf s)] at this
    exact this
  empty_parity s _ _ _ _ _ _ _ he := by
    have := (ht.poll (Frame.lt_of_get hX he) he (partner_ring (hf s))).2.2.2.1
    rw [pollOffset_partner (hf s)] at this
    exact this
  spins := by
    intro w pc m q acq sc he
    obtain ⟨g, k⟩ := w
    exact ht.spins (Frame.lt_of_get hX he) he
  full_acq s _ _ _ _ _ _ he := (ht.poll (Frame.lt_of_get hX he) he (isFull_ring (hf s))).2.2.2.2 rfl
  empty_acq s _ _ _ _ _ _ _ he :=
    (ht.poll (Frame.lt_of_get hX he) he (partner_ring (hf s))).2.2.2.2 rfl
  cluster a i := by
    have h1 := clusterOf_eq hpre ((slot L X c (.kvFull 0)).prod a)
    have h2 := clusterOf_eq hpre ((slot L X c (.kvFull 0)).cons i)
    rw [ctaOf_lead hpre a] at h1
    rw [ctaOf_cons hpre i] at h2
    simp only [clusterOf, ctaOf] at h1 h2
    change L.clusterOfCta (leadOf L X (2 * c + a.val) 14 / L.block) =
      L.clusterOfCta (leadOf L X (2 * c) 12 / L.block)
    simp only [slot] at h1 h2
    rw [h1, h2]
    omega

/-- **The hypotheses of slot `b` of pair `c`**: those of the slot of the Q or KV ring
declaration (`PairTmaRing.Decl.hyp`). -/
theorem hyp (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X)
    (htm : TmemFacts L X) (hinit : RingInit L X) (hb : b.isFull) (c : Nat) :
    PairTmaRing.Hyp L kernel asms X (slot L X c b) := by
  cases b with
  | qFull st => exact (qDecl L X c).hyp hX (events hpre hX ht htm hinit (fun _ => rfl) c) st
  | kvFull s => exact (kvDecl L X c).hyp hX (events hpre hX ht htm hinit (fun _ => rfl) c) s
  | _ => cases hb

end Rings

end
end PTX.Kernels.FlashAttn4Fwd.Proof
