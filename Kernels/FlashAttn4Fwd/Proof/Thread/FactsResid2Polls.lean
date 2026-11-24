-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreOut

@[expose] public section

/-! # Which warps poll and arrive on which barriers

Every poll and every arrival names a barrier of the table in some CTA, and the barrier's kind
determines the warp that makes the event (`wait_by`, `arrive_by`). An event of a kind the
prologue does not fire is fired by a role state (`role_event`), and each role's poll and arrival
sites name only its own barriers:

* the loader polls the ring empty barriers and arrives on the ring full barriers
  (`Loader.wait_fact`, `Loader.arrive_fact`);
* the MMA warp polls the ring full, P-ready, second P-ready and handshake barriers and arrives on
  the peer's handshake barrier (`wait_ev`, `arrive_ev`);
* the softmax warps poll the statistics credit and S-full barriers and arrive on the leader's
  P-ready and second P-ready barriers (`Softmax.Ev`);
* the correction warps poll the O-full and free barriers and arrive on the credit, staged and the
  leader's P-ready barriers (`corr_wait`, `corr_arrive`);
* the store warp polls the staged barriers and arrives on the free barriers
  (`Store.Ev`);
* the idle warp has no poll and no arrival site (`Idle.site_not_poll`).

No thread arrives on an S-full, O-full, ring empty or spare barrier: those complete by commits
only. The other roles' parts of the per-warp poll and arrival fields follow (`*_other`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The warps that poll barrier `b`. -/
def WaitBy (w : Nat) : FBar → Prop
  | .qEmpty _ | .kvEmpty _ => w = 14
  | .qFull _ | .kvFull _ | .pReady _ | .pReady2 _ | .dealloc => w = 12
  | .stats _ | .sFull _ => w < 8
  | .oFull _ | .oFree _ => 8 ≤ w ∧ w < 12
  | .oStaged _ => w = 13
  | .spare _ _ => False

/-- The warps that arrive on barrier `b`. -/
def ArriveBy (w : Nat) : FBar → Prop
  | .qFull _ | .kvFull _ => w = 14
  | .dealloc => w = 12
  | .pReady _ => w < 12
  | .pReady2 _ => w < 8
  | .stats _ | .oStaged _ => 8 ≤ w ∧ w < 12
  | .oFree _ => w = 13
  | _ => False

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **Every poll** is of a barrier of the table whose kind names the thread's warp. -/
theorem wait_by {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ WaitBy (warpOf L g) b := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨r, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h) (fun h => h)
  have hw := Cross.role_of_state hpre hX hg hσ
  have hk : (⟨pc, .wait m p ok acq sc⟩ : Event).kind = .wait m p ok acq sc := rfl
  cases r with
  | store d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨st, -, rfl, -⟩ := Store.ev_wait (Store.shape hpre hat hi hc hf)
    refine ⟨.oStaged st, ctaOf L g, ?_, hw⟩
    rw [Store.stagedAt_eq, stagedBar_fbar L _ st.isLt]
  | loader d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨b, hb, hm, -⟩ := Loader.wait_fact hpre hg hJ hi
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf hk
    refine ⟨b, _, hm, ?_⟩
    cases b <;> simp_all [FBar.isEmpty, WaitBy]
  | mma d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨B, hpb, hm, -⟩ := wait_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hf) hk
    refine ⟨B, _, hm, ?_⟩
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp only [Mma.pollBar, reduceCtorEq, Option.some.injEq] at hpb <;>
      subst hpb <;> exact hw
  | softmax d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    have hev := Softmax.site_event hpre hg hi hat hc hf
    have hst : warpOf L g / 4 < 2 := by omega
    obtain ⟨site, i', tt, sc', m', l'⟩ := d
    cases site <;> simp only [Softmax.Ev, Kind.wait.injEq, reduceCtorEq, exists_false] at hev
    · obtain ⟨-, -, -, -, rfl, -⟩ := hev
      exact ⟨.stats ⟨_, hst⟩, ctaOf L g, by simp [FBar.loc, FBar.off], hw⟩
    · obtain ⟨-, -, -, -, rfl, -⟩ := hev
      exact ⟨.sFull ⟨_, hst⟩, ctaOf L g, by simp [FBar.loc, FBar.off], hw⟩
  | corr d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨d', -, -, -, -, h⟩ := corr_wait hpre hX ht hw.1 hw.2 he
    rcases h with ⟨st, -, rfl, -⟩ | ⟨st, -, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact ⟨.oFull st, ctaOf L g, by simp [FBar.loc, FBar.off], hw⟩
    · exact ⟨.oFree st, ctaOf L g, by simp [FBar.loc, FBar.off], hw⟩
    · exact ⟨.oFree 1, ctaOf L g, by simp [FBar.loc, FBar.off], hw⟩
  | idle s =>
    exfalso
    obtain ⟨p', b, off, par, sc0, hop, -⟩ := fires_wait_flags hf hk
    exact (Idle.site_not_poll s.site).1 (OpPcsFast.mem kernel_poll_pcs hc (by rw [hop]; rfl))

/-- **Every arrival** is on a barrier of the table whose kind names the thread's warp. -/
theorem arrive_by {g k pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩) :
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ ArriveBy (warpOf L g) b := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨r, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h) (fun h => h)
  have hw := Cross.role_of_state hpre hX hg hσ
  have hk : (⟨pc, .arrive m tx cnt rel sc⟩ : Event).kind = .arrive m tx cnt rel sc := rfl
  cases r with
  | store d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨st, -, rfl, -⟩ := Store.ev_arrive (Store.shape hpre hat hi hc hf)
    refine ⟨.oFree st, ctaOf L g, ?_, hw⟩
    rw [Store.freeAt_eq, freeBar_fbar L _ st.isLt]
  | loader d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨b, hb, hm, -⟩ := Loader.arrive_fact hpre hg hJ hi
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf hk
    refine ⟨b, _, hm, ?_⟩
    cases b <;> simp_all [FBar.isFull, ArriveBy]
  | mma d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨-, hm, -⟩ := arrive_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hf) hk
    exact ⟨.dealloc, _, hm, hw⟩
  | softmax d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    have hev := Softmax.site_event hpre hg hi hat hc hf
    have hst : warpOf L g / 4 < 2 := by omega
    obtain ⟨site, i', tt, sc', m', l'⟩ := d
    cases site <;> simp only [Softmax.Ev, Kind.arrive.injEq, reduceCtorEq,
      exists_false] at hev
    · obtain ⟨-, -, -, -, rfl, -⟩ := hev
      exact ⟨.pReady ⟨_, hst⟩, 2 * (ctaOf L g / 2), by simp [FBar.loc, FBar.off],
        by simp only [ArriveBy]; omega⟩
    · obtain ⟨-, -, -, -, rfl, -⟩ := hev
      exact ⟨.pReady2 ⟨_, hst⟩, 2 * (ctaOf L g / 2), by simp [FBar.loc, FBar.off], hw⟩
  | corr d =>
    simp only [Role.kind, RoleKind.Warp] at hw
    obtain ⟨-, -, d', -, -, -, -, h⟩ := corr_arrive hpre hX ht hw.1 hw.2 he
    rcases h with ⟨a, -, rfl⟩ | ⟨st, -, rfl⟩ | ⟨st, -, rfl⟩
    · exact ⟨.stats ⟨a.val % 2, Nat.mod_lt _ (by decide)⟩, ctaOf L g,
        by simp [FBar.loc, FBar.off], hw⟩
    · exact ⟨.oStaged st, ctaOf L g, by simp [FBar.loc, FBar.off], hw⟩
    · exact ⟨.pReady st, 2 * (ctaOf L g / 2), by simp [FBar.loc, FBar.off],
        by simp only [ArriveBy]; omega⟩
  | idle s =>
    exfalso
    obtain ⟨b, off, tx', c', cl, sc0, st', hop, -⟩ := fires_arrive_flags hf hk
    exact (Idle.site_not_poll s.site).2 (OpPcsFast.mem kernel_arrive_pcs hc (by rw [hop]; rfl))

/-- A poll of barrier `b` in CTA `c` is made by a warp `WaitBy` names. -/
theorem wait_by_of {g k pc p c : Nat} {b : FBar} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (b.loc L c) p ok acq sc⟩) : WaitBy (warpOf L g) b := by
  obtain ⟨b', c', hm, hw⟩ := wait_by hpre hX ht he
  rwa [(FBar.loc_inj hm).1]

/-- An arrival on barrier `b` in CTA `c` is made by a warp `ArriveBy` names. -/
theorem arrive_by_of {g k pc tx cnt c : Nat} {b : FBar} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive (b.loc L c) tx cnt rel sc⟩) :
    ArriveBy (warpOf L g) b := by
  obtain ⟨b', c', hm, hw⟩ := arrive_by hpre hX ht he
  rwa [(FBar.loc_inj hm).1]

/-! ### The other roles' parts of the poll and arrival fields -/

/-- `TmemFacts.hs_arrive`, warps other than 12. -/
theorem TmemFacts_hs_arrive_other :
    ∀ {g k pc tx c cta : Nat} {m : Loc} {rel : Bool} {sc : MbarScope},
      g < L.threads → warpOf L g ≠ 12 → X.get (g, k) = some ⟨pc, .arrive m tx c rel sc⟩ →
      m = FBar.loc L cta .dealloc →
        warpOf L g = 12 ∧ cta = pairCta (ctaOf L g) ∧ tx = 0 ∧ c = 1 ∧
          ∀ k' pc' tx' c' rel' sc', X.get (g, k') = some ⟨pc', .arrive m tx' c' rel' sc'⟩ →
            k' = k := by
  intro g k pc tx c cta m rel sc _ h12 he hm
  subst hm
  exact absurd (arrive_by_of hpre hX ht he) h12

/-- `TmemFacts.hs_wait`, warps other than 12. -/
theorem TmemFacts_hs_wait_other :
    ∀ {g k pc p cta : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope},
      g < L.threads → warpOf L g ≠ 12 → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      m = FBar.loc L cta .dealloc → warpOf L g = 12 ∧ cta = ctaOf L g ∧ p = 0 := by
  intro g k pc p cta m ok acq sc _ h12 he hm
  subst hm
  exact absurd (wait_by_of hpre hX ht he) h12

/-- `RingFacts.poll`, warps other than 12 and 14. -/
theorem RingFacts_poll_other :
    ∀ {g k pc p c : Nat} {b : FBar} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g ≠ 12 → warpOf L g ≠ 14 →
      X.get (g, k) = some ⟨pc, .wait (b.loc L c) p ok acq sc⟩ → b.ring →
        c = ctaOf L g ∧ (b.isFull → warpOf L g = 12 ∧ ctaOf L g % 2 = 0) ∧
        (b.isEmpty → warpOf L g = 14) ∧
        p % 2 = (okPolls (b.loc L c) ((X.tr g).take k) + b.pollOffset) % 2 ∧
        (ok = true → acq = true ∧ sc = .cluster) := by
  intro g k pc p c b ok acq sc _ h12 h14 he hb
  have hw := wait_by_of hpre hX ht he
  exfalso
  cases b <;> simp_all [WaitBy, FBar.ring]

/-- `RingFacts.arrive`, warps other than 14. -/
theorem RingFacts_arrive_other :
    ∀ {g k pc tx cnt c : Nat} {b : FBar} {rel : Bool} {sc : MbarScope},
      g < L.threads → warpOf L g ≠ 14 →
      X.get (g, k) = some ⟨pc, .arrive (b.loc L c) tx cnt rel sc⟩ → b.ring →
        b.isFull ∧ c = ctaOf L g ∧ ctaOf L g % 2 = 0 ∧ warpOf L g = 14 ∧ LeadAt L X g k ∧
        tx = b.useBytes ∧ cnt = 1 ∧
        arrivals (b.loc L c) ((X.tr g).take k) + 1 ≤
          okPolls (b.partner.loc L c) ((X.tr g).take k) := by
  intro g k pc tx cnt c b rel sc _ h14 he hb
  have hw := arrive_by_of hpre hX ht he
  exfalso
  cases b <;> simp_all [ArriveBy, FBar.ring]

/-- `StatsFacts.credit_arrive`, warps other than 8-11. -/
theorem StatsFacts_credit_arrive_other :
    ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
      ¬ (8 ≤ warpOf L g ∧ warpOf L g < 12) → st < 2 →
      X.get (g, i) = some ⟨pc, .arrive (statsBar L c st) tx cnt rel sc⟩ →
        8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true := by
  intro g i pc tx cnt c st rel sc _ hw hst he
  rw [statsBar_eq L c ⟨st, hst⟩] at he
  exact absurd (arrive_by_of hpre hX ht he) hw

/-- `OutputFacts.staged_arrive`, warps other than 8-11. -/
theorem OutputFacts_staged_arrive_other :
    ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
      ¬ (8 ≤ warpOf L g ∧ warpOf L g < 12) → st < 2 →
      X.get (g, i) = some ⟨pc, .arrive (stagedBar L c st) tx cnt rel sc⟩ →
        8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
        arrivals (stagedBar L c st) ((X.tr g).take i) + 1 ≤
          okPolls (freeBar L c st) ((X.tr g).take i) := by
  intro g i pc tx cnt c st rel sc _ hw hst he
  rw [stagedBar_fbar L c hst] at he
  exact absurd (arrive_by_of hpre hX ht he) hw

/-- `OutputFacts.free_poll`, warps other than 8-11. -/
theorem OutputFacts_free_poll_other :
    ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      ¬ (8 ≤ warpOf L g ∧ warpOf L g < 12) → st < 2 →
      X.get (g, i) = some ⟨pc, .wait (freeBar L c st) p ok acq sc⟩ →
        8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧
        p % 2 = (okPolls (freeBar L c st) ((X.tr g).take i) + 1) % 2 ∧
        (ok = true → acq = true) := by
  intro g i pc p c st ok acq sc _ hw hst he
  rw [freeBar_fbar L c hst] at he
  exact absurd (wait_by_of hpre hX ht he) hw

/-- `PReadyFacts.p_arrive`, warps 12-15. -/
theorem PReadyFacts_p_arrive_other :
    ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
      12 ≤ warpOf L g → st < 2 →
      X.get (g, i) = some ⟨pc, .arrive (pReadyBar L c st) tx cnt rel sc⟩ →
        leadCta (ctaOf L g) = c ∧
          ((warpOf L g < 8 ∧ warpOf L g / 4 = st) ∨ (8 ≤ warpOf L g ∧ warpOf L g < 12)) ∧
          tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cluster := by
  intro g i pc tx cnt c st rel sc _ hw hst he
  rw [pReadyBar_eq L c ⟨st, hst⟩] at he
  have h := arrive_by_of hpre hX ht he
  simp only [ArriveBy] at h
  omega

/-- `PReadyFacts.p_poll`, warps other than 12. -/
theorem PReadyFacts_p_poll_other :
    ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g ≠ 12 → st < 2 →
      X.get (g, i) = some ⟨pc, .wait (pReadyBar L c st) p ok acq sc⟩ →
        ctaOf L g = c ∧ warpOf L g = 12 ∧
          p % 2 = okPolls (pReadyBar L c st) ((X.tr g).take i) % 2 ∧
          (ok = true → acq = true ∧ sc = .cluster) := by
  intro g i pc p c st ok acq sc _ h12 hst he
  rw [pReadyBar_eq L c ⟨st, hst⟩] at he
  exact absurd (wait_by_of hpre hX ht he) h12

/-- `P2Facts.p2_poll`, warps other than 12. -/
theorem P2Facts_p2_poll_other :
    ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g ≠ 12 → st < 2 →
      X.get (g, i) = some ⟨pc, .wait (pReady2Bar L c st) p ok acq sc⟩ →
        ctaOf L g = c ∧ warpOf L g = 12 ∧
          p % 2 = okPolls (pReady2Bar L c st) ((X.tr g).take i) % 2 ∧
          (ok = true → acq = true ∧ sc = .cluster) := by
  intro g i pc p c st ok acq sc _ h12 hst he
  rw [pReady2Bar_eq L c ⟨st, hst⟩] at he
  exact absurd (wait_by_of hpre hX ht he) h12

/-- **`SFullFacts.s_arrive`**: no thread arrives on an S-full barrier. -/
theorem SFullFacts_s_arrive :
    ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, st < 2 →
      X.get (g, i) ≠ some ⟨pc, .arrive (sFullBar L c st) tx cnt rel sc⟩ := by
  intro g i pc tx cnt c st rel sc hst he
  rw [sFullBar_eq L c ⟨st, hst⟩] at he
  exact arrive_by_of hpre hX ht he

/-- **`OFullFacts.o_arrive`**: no thread arrives on an O-full barrier. -/
theorem OFullFacts_o_arrive :
    ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, st < 2 →
      X.get (g, i) ≠ some ⟨pc, .arrive (oFullBar L c st) tx cnt rel sc⟩ := by
  intro g i pc tx cnt c st rel sc hst he
  rw [oFullBar_eq L c ⟨st, hst⟩] at he
  exact arrive_by_of hpre hX ht he

/-- `OFullFacts.o_poll`, warps other than 8-11. -/
theorem OFullFacts_o_poll_other :
    ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      ¬ (8 ≤ warpOf L g ∧ warpOf L g < 12) → st < 2 →
      X.get (g, i) = some ⟨pc, .wait (oFullBar L c st) p ok acq sc⟩ →
        ctaOf L g = c ∧ 8 ≤ warpOf L g ∧ warpOf L g < 12 ∧
          p % 2 = okPolls (oFullBar L c st) ((X.tr g).take i) % 2 ∧
          (ok = true → acq = true ∧ sc = .cluster) := by
  intro g i pc p c st ok acq sc _ hw hst he
  rw [oFullBar_eq L c ⟨st, hst⟩] at he
  exact absurd (wait_by_of hpre hX ht he) hw

/-- `TmemLifeFacts.hs_release`, warps other than 12. -/
theorem TmemLifeFacts_hs_release_other :
    ∀ {g y pc tx c cta : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g ≠ 12 →
      X.get (g, y) = some ⟨pc, .arrive (FBar.loc L cta .dealloc) tx c rel sc⟩ →
        rel = true ∧ sc = .cluster ∧ ∃ b < y, Bar2Sync X g b 1 := by
  intro g y pc tx c cta rel sc _ h12 he
  exact absurd (arrive_by_of hpre hX ht he) h12

/-- `ExitFacts.hs_arrive`, warps other than 12. -/
theorem ExitFacts_hs_arrive_other :
    ∀ {g k pc tx cnt cta : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g ≠ 12 →
      X.get (g, k) = some ⟨pc, .arrive (FBar.loc L cta .dealloc) tx cnt rel sc⟩ →
        rel = true ∧ sc = .cluster ∧
          ∃ i < k, ∃ pci cnti, X.IsBarrier (g, i) 2 cnti pci ∧ barOrd X g i 2 = 1 := by
  intro g k pc tx cnt cta rel sc _ h12 he
  exact absurd (arrive_by_of hpre hX ht he) h12

/-- `ExitFacts.hs_wait`, warps other than 12. -/
theorem ExitFacts_hs_wait_other :
    ∀ {g k pc p cta : Nat} {acq : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g ≠ 12 →
      X.get (g, k) = some ⟨pc, .wait (FBar.loc L cta .dealloc) p true acq sc⟩ →
        acq = true ∧ sc = .cluster := by
  intro g k pc p cta acq sc _ h12 he
  exact absurd (wait_by_of hpre hX ht he) h12

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
