-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccess
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotAsyncArrive
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderCopy
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCluster

@[expose] public section

/-! # Which roles access memory and name barriers (`OlderFacts`, `AsyncFacts`, `SpareUnused`)

* **Accesses.** The kernel's loads and stores are at the sites of the softmax, correction and MMA
  roles only (`kernel_mem_pcs`; no prologue, loader, store or idle site is one), so every access
  is a thread's of warps 0-12 (`access_warp13`). The ranges of those roles' accesses are their
  packages' facts (`LowAccessLow`, `BaseFree`, `MmaBaseWrite`, `MmaBaseRead`); with them the
  region fields follow (`OlderFacts_access_low`, `OlderFacts_base_write`, `OlderFacts_base_read`).
* **Barriers.** The kernel has no bulk copy and no invalidation (`kernel_no_bulk`,
  `kernel_no_inval`), so an mbarrier is used by an arrival, a poll or a commit. A commit's
  targets are ring empty, S-full or O-full barriers of the issuer's pair (the fields
  `ExitFacts.commit_target` and `InitFacts.commit_cluster`, premises `CommitTargets` and
  `CommitCluster`); arrivals and polls name table barriers that are not spare, of the issuer's
  pair, by each role's sites (`SyncNamed`). So every use names a table barrier of the pair
  (`AsyncFacts_mbar_pair`) and none a spare one (`SpareUnused_holds`, the statement of
  `Safety.SpareUnused`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Accesses come from warps 0-12 -/

/-- The positions of the `ld.param` loads. They are local steps, so no site is among them. -/
abbrev paramLoadPcs : List Nat := [0, 5, 6, 7, 8, 9, 10, 193, 540, 1129, 1205, 1241, 2709, 3753]

/-- The positions of the loads and stores (allocations store the Tensor Memory address). -/
abbrev memPcs : List Nat :=
  Flow.load.toList ++ Flow.store.toList ++ Flow.tmemAlloc.toList ++ paramLoadPcs

/-- Every load and store of the kernel is listed. -/
theorem kernel_mem_pcs : OpPcsFast kernel.code (fun op => readOp op || writeOp op) memPcs =
    true := by
  decide +kernel

theorem Prologue.site_not_mem (s : Prologue.Site) : s.pc ∉ memPcs := by
  cases s <;> site_decide

theorem Loader.site_not_mem (s : Loader.Site) : s.pc ∉ memPcs := by
  cases s <;> site_decide

theorem Store.site_not_mem (s : Store.Site) : s.pc ∉ memPcs := by
  cases s <;> site_decide

theorem Idle.site_not_mem (s : Idle.Site) : s.pc ∉ memPcs := by
  cases s <;> site_decide

/-- **Every access is a thread's of warps 0-12.** -/
theorem access_warp13 (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {a : Acc} {w : Bool}
    (h : X.Access (g, k) a w) : warpOf L g < 13 := by
  obtain ⟨e, he, hop⟩ : ∃ e, X.get (g, k) = some e ∧ ∀ {A L g t op pc o},
      Fires pc (eventTmpl A L g t op) e o → (readOp op || writeOp op) = true := by
    rcases access_rw hX h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩
    · refine ⟨_, he, fun {A L g t op pc o} hf => ?_⟩
      obtain ⟨k', hm⟩ := fires_read_tmpl hf
      cases hq : readOp op
      · have hn := eventTmpl_notRead (A := A) (L := L) (g := g) (t := t) hq
        rw [hm] at hn
        exact hn.elim
      · rfl
    · exact ⟨_, he, fun hf => by rw [fires_write_op hf rfl]; simp⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he
      (by rintro pc f rfl; rcases access_rw hX h with ⟨bs, ⟨_, he'⟩, -⟩ | ⟨bs, ⟨_, he'⟩, -⟩ <;>
        rw [he] at he' <;> cases he')
  have hpc := OpPcsFast.mem kernel_mem_pcs hc (hop hf)
  rcases d with p | r
  · exact absurd hpc (Prologue.site_not_mem p.site)
  have hk := role_of_state hpre hX hg hσ
  cases r with
  | idle s => exact absurd hpc (Idle.site_not_mem s.site)
  | loader l => exact absurd hpc (Loader.site_not_mem l.site)
  | store s => exact absurd hpc (Store.site_not_mem s.site)
  | _ => simp only [Role.kind, RoleKind.Warp] at hk; omega

/-- The accesses of warps 0-12 lie below the ring regions (per role: the softmax statistics
words, the correction warps' statistics loads and staging stores, warp 12's base word). -/
def LowAccessLow (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {a : Acc} {w : Bool} {l : Loc}, warpOf L g < 13 → X.Access (g, k) a w →
    a.Covers l → l.addr < L.sharedBase + 68608

/-- **A thread's access lies below the ring regions.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.OlderFacts_access_low (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X)
    (hlow : LowAccessLow L X) :
    ∀ {g k : Nat} {a : Acc} {w : Bool} {l : Loc}, X.Access (g, k) a w → a.Covers l →
      l.addr < L.sharedBase + 68608 :=
  fun h hc => hlow (access_warp13 hpre hX ht h) h hc

/-- The softmax and correction warps' accesses do not cover the base word (per role: the
statistics words start at `+332`, the staging buffers above them). -/
def BaseFree (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {a : Acc} {w : Bool} {l : Loc}, warpOf L g < 12 → X.Access (g, k) a w →
    a.Covers l → L.sharedBase + 328 ≤ l.addr → l.addr < L.sharedBase + 332 → False

/-- Warp 12's part of `base_write` (MMA package: its writes are lane 0's allocation store). -/
def MmaBaseWrite (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {a : Acc} {bs : List Byte} {l : Loc}, warpOf L g = 12 → X.Writes (g, k) a bs →
    a.Covers l → L.sharedBase + 328 ≤ l.addr → l.addr < L.sharedBase + 332 →
      g % L.block = 384 ∧ a.loc = baseLoc L (ctaOf L g) ∧ a.size = 4 ∧ bs.length = 4 ∧
        barOrd X g k 2 = 0 ∧
        ∃ j pc grp dst n, k = j + 1 ∧
          X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩

/-- Warp 12's part of `base_read` (MMA package: its reads of the base word follow its start
barrier). -/
def MmaBaseRead (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {a : Acc} {bs : List (Option Byte)} {l : Loc}, warpOf L g = 12 →
    X.Reads (g, k) a bs → a.Covers l → L.sharedBase + 328 ≤ l.addr →
    l.addr < L.sharedBase + 332 → ∃ b < k, Bar2Sync X g b 0

/-- **A write of a base-word byte is lane 0 of warp 12's allocation store.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.OlderFacts_base_write (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X)
    (hfree : BaseFree L X) (hmma : MmaBaseWrite L X) :
    ∀ {g k : Nat} {a : Acc} {bs : List Byte} {l : Loc}, X.Writes (g, k) a bs →
      a.Covers l → L.sharedBase + 328 ≤ l.addr → l.addr < L.sharedBase + 332 →
        g % L.block = 384 ∧ a.loc = baseLoc L (ctaOf L g) ∧ a.size = 4 ∧ bs.length = 4 ∧
          barOrd X g k 2 = 0 ∧
          ∃ j pc grp dst n, k = j + 1 ∧
            X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ := by
  intro g k a bs l hw hc h1 h2
  have hA : X.Access (g, k) a true := .inr (.inl ⟨bs, hw, rfl⟩)
  have h13 := access_warp13 hpre hX ht hA
  by_cases h12 : warpOf L g = 12
  · exact hmma h12 hw hc h1 h2
  · exact (hfree (by omega) hA hc h1 h2).elim

/-- **A read of a base-word byte is warp 12's, after its start barrier.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.OlderFacts_base_read (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X)
    (hfree : BaseFree L X) (hmma : MmaBaseRead L X) :
    ∀ {g k : Nat} {a : Acc} {bs : List (Option Byte)} {l : Loc}, X.Reads (g, k) a bs →
      a.Covers l → L.sharedBase + 328 ≤ l.addr → l.addr < L.sharedBase + 332 →
        warpOf L g = 12 ∧ ∃ b < k, Bar2Sync X g b 0 := by
  intro g k a bs l hr hc h1 h2
  have hA : X.Access (g, k) a false := .inl ⟨bs, hr, rfl⟩
  have h13 := access_warp13 hpre hX ht hA
  by_cases h12 : warpOf L g = 12
  · exact ⟨h12, hmma h12 hr hc h1 h2⟩
  · exact (hfree (by omega) hA hc h1 h2).elim

/-! ### The barriers the threads name -/

/-- The kernel has no bulk copy. -/
theorem kernel_no_bulk : OpPcsFast kernel.code bulkOp [] = true := by
  decide +kernel

/-- The kernel has no invalidation. -/
theorem kernel_no_inval : OpPcsFast kernel.code invalOp [] = true := by
  decide +kernel

/-- Every arrival and every poll names a table barrier that is not spare, of a CTA of the
issuer's pair (per role: the barrier operands of the arrival and poll sites, the roles' `Ev`). -/
def SyncNamed (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {m : Loc} {kd : Kind}, g < L.threads → X.get (g, k) = some ⟨pc, kd⟩ →
    ((∃ tx c rel sc, kd = .arrive m tx c rel sc) ∨
      (∃ p ok acq sc, kd = .wait m p ok acq sc)) →
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L g / 2 ∧
      ∀ i st, b ≠ .spare i st

/-- The field `ExitFacts.commit_target` (MMA package). -/
def CommitTargets (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m →
      ∃ (b : FBar) (c : Nat), m = b.loc L c ∧
        (b.isEmpty ∨ ∃ st, b = .sFull st ∨ b = .oFull st)

/-- The field `InitFacts.commit_cluster` (`initFacts`). -/
def CommitCluster (L : Launch) (X : Execution) : Prop :=
  ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc},
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m →
      m.cta / 2 = ctaOf L i.1 / 2

/-- The kernel issues no cancellation request. -/
theorem uses_no_clc : OpPcsFast kernel.code clcOp [] = true := by
  decide +kernel

/-- The kernel has no `cp.async.mbarrier.arrive`. -/
theorem uses_no_asyncArrive : OpPcsFast kernel.code asyncArriveOp [] = true := by
  decide +kernel

/-- An mbarrier use is an arrival, a poll, a commit's target, a tensor copy's barrier or an
initialization. -/
theorem uses_cases (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {e : EvId} {m : Loc} (h : X.UsesMbar e m) :
    (∃ pc kd, X.get e = some ⟨pc, kd⟩ ∧
      ((∃ tx c rel sc, kd = .arrive m tx c rel sc) ∨
        (∃ p ok acq sc, kd = .wait m p ok acq sc))) ∨
    (∃ pc sp r, X.get e = some ⟨pc, .tc (.commit sp)⟩ ∧ TcCommit.target sp r = some m) ∨
    (∃ address s, X.TensorIssue e address s ∧ s.mbar = m) ∨ (∃ count, X.MbInit e m count) := by
  obtain ⟨g, k⟩ := e
  have none_of : ∀ {pc : Nat} {kd : Kind} {p : Op → Bool},
      X.get (g, k) = some ⟨pc, kd⟩ → (∀ f, kd ≠ .ub f) →
      OpPcsFast kernel.code p [] = true →
      (∀ {A L g t op q o}, Fires q (eventTmpl A L g t op) ⟨pc, kd⟩ o → p op = true) →
      False := by
    intro pc kd p he hub hk hop
    obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
      event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he
        (fun pc' f h => hub f (by cases h; rfl))
    exact absurd (OpPcsFast.mem hk hc (hop hf)) (List.not_mem_nil)
  rcases h with ⟨tx, c, rel, sc, pc, he⟩ | ⟨s, ⟨pc, he⟩, -⟩ | ⟨noinc, pc, he⟩ |
      ⟨sp, r, ⟨pc, he⟩, ht'⟩ | ⟨pc, q, ok, acq, sc, he⟩ | ⟨pc, he⟩ | ⟨address, s, hti, hs⟩ |
      ⟨s, targets, c, ⟨pc, he⟩, -⟩ | ⟨count, hin⟩
  · exact .inl ⟨pc, _, he, .inl ⟨tx, c, rel, sc, rfl⟩⟩
  · exact (none_of he (fun _ h => by cases h) kernel_no_bulk fun hf => fires_bulk_op hf rfl).elim
  · exact (none_of he (fun _ h => by cases h) uses_no_asyncArrive
      fun hf => fires_asyncArrive_op hf rfl).elim
  · exact .inr (.inl ⟨pc, sp, r, he, ht'⟩)
  · exact .inl ⟨pc, _, he, .inr ⟨q, ok, acq, sc, rfl⟩⟩
  · exact (none_of he (fun _ h => by cases h) kernel_no_inval
      fun hf => fires_mbInval_op hf rfl).elim
  · exact .inr (.inr (.inl ⟨address, s, hti, hs⟩))
  · exact (none_of he (fun _ h => by cases h) uses_no_clc
      fun hf => fires_clcIssue_op hf rfl).elim
  · exact .inr (.inr (.inr ⟨count, hin⟩))

/-- **Every mbarrier operation names a table barrier of a CTA of its issuer's pair.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.AsyncFacts_mbar_pair (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X)
    (hsync : SyncNamed L X) (hct : CommitTargets L X) (hcc : CommitCluster L X) :
    ∀ {e : EvId} {m : Loc}, X.UsesMbar e m →
      ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L e.1 / 2 := by
  intro e m h
  obtain ⟨g, k⟩ := e
  rcases uses_cases hpre hX ht h with ⟨pc, kd, he, hk⟩ | ⟨pc, sp, r, he, htg⟩ |
      ⟨address, s, ⟨pc, he⟩, hs⟩ | ⟨count, pc, he⟩
  · obtain ⟨b, c, hm, hc, -⟩ := hsync (Frame.lt_of_get hX he) he hk
    exact ⟨b, c, hm, hc⟩
  · obtain ⟨b, c, hm, -⟩ := hct (Frame.lt_of_get hX he) he htg
    have h2 := hcc he htg
    rw [hm] at h2
    exact ⟨b, c, hm, h2⟩
  · -- a tensor copy completes on a ring barrier of the even CTA of the pair
    obtain ⟨d, -, -, -, -, -, u, j, -, hci, -⟩ := Loader.copy_origin hpre hX ht he
    refine ⟨_, Loader.evenCta L g, by rw [← hs]; exact hci.mbar, ?_⟩
    show 2 * (ctaOf L g / 2) / 2 = ctaOf L g / 2
    omega
  · -- an initialization is of a table barrier of the thread's CTA
    obtain ⟨b, hm, -⟩ := ClusterFacts_init_site hpre hX ht (Frame.lt_of_get hX he) he
    exact ⟨b, ctaOf L g, hm, rfl⟩

theorem FBar.target_not_spare :
    ∀ b : FBar, (b.isEmpty ∨ ∃ st, b = .sFull st ∨ b = .oFull st) →
    ∀ i st, b ≠ .spare i st := by
  decide

/-- **No operation but an initialization names a spare barrier.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.SpareUnused_holds (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X)
    (hsync : SyncNamed L X) (hct : CommitTargets L X) :
    ∀ {e : EvId} {m : Loc}, X.UsesMbar e m → (¬ ∃ count, X.MbInit e m count) →
      ∀ k st c, m ≠ (FBar.spare k st).loc L c := by
  intro e m h hni i st c hm
  obtain ⟨g, k⟩ := e
  rcases uses_cases hpre hX ht h with ⟨pc, kd, he, hk⟩ | ⟨pc, sp, r, he, htg⟩ |
      ⟨address, s, ⟨pc, he⟩, hs⟩ | hin
  · obtain ⟨b, c', hb, -, hns⟩ := hsync (Frame.lt_of_get hX he) he hk
    exact hns i st (FBar.loc_inj (hb.symm.trans hm)).1
  · obtain ⟨b, c', hb, hcls⟩ := hct (Frame.lt_of_get hX he) he htg
    exact FBar.target_not_spare b hcls i st (FBar.loc_inj (hb.symm.trans hm)).1
  · exact Loader.copy_mbar_ne hpre hX ht he (b := .spare i st) rfl c (hs.trans hm)
  · exact hni hin

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
