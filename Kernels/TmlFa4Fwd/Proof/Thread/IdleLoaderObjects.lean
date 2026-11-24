-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRoute
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseSource
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryDrainRelease
public import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner
import Kernels.TmlFa4Fwd.Proof.Thread.IdleOutputFree
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Barrier
import Lemmas.Step.CtaBarNamed
import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader (emptySlot)

noncomputable section

/-- The release objects that the loader drains when its CTA has no scheduled tile. -/
inductive IdleReleaseObject
  | cache (slot : Fin 3)
  | secondQuery

/-- The common prologue slot that initializes an idle drain object. -/
def IdleReleaseObject.initializer : IdleReleaseObject → Fin 34
  | .cache slot => emptySlot slot
  | .secondQuery => 3

/-- A cache slot's release object or the return object for the second query buffer. -/
def IdleReleaseObject.loc (l : Launch) (cta : Nat) (obj : IdleReleaseObject) : Loc :=
  initObject l cta obj.initializer

theorem IdleReleaseObject.cacheLoc (l : Launch) (g : Nat) (slot : Fin 3) :
    (IdleReleaseObject.cache slot).loc l (g/l.block) =
      Thread.Mma.Observation.emptyObject l g slot := rfl

theorem IdleReleaseObject.queryLoc (l : Launch) (cta : Nat) :
    IdleReleaseObject.secondQuery.loc l cta = secondQueryEmpty l cta := rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Maximal startup installs each empty release object with one pending arrival. -/
theorem idleReleaseInitialized (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (hc : cta < l.grid) (obj : IdleReleaseObject) :
    PairTmaRing.InitFirst X (obj.loc l cta) 1 ∧
      ∃ r ∈ X.objects (obj.loc l cta), r.action = .init 1 := by
  let g := cta*l.block + 0
  have hb : 0 < l.block := by rw [hp.block]; decide
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hb
  obtain ⟨hCTA,hLocal⟩ := NamedBar.lane_cta (c := cta) hb hb
  have hw : warpIndex l g = 0 := by unfold warpIndex g; rw [hLocal]
  obtain ⟨a,_,hSame,_,_,hInit⟩ := warp0InitializerRecords hp hMax hg hw
  have ha : a/l.block = cta := hSame.1.2.2.symm.trans hCTA
  let site := obj.initializer
  have hCount : (initSite site).count = 1 := by cases obj with
    | cache slot => fin_cases slot <;> rfl
    | secondQuery => rfl
  obtain ⟨j,_,he⟩ := hInit site
  have hExpected : (initEvent l a site).kind = .mbInit (obj.loc l cta) 1 := by
    change Kind.mbInit (initObject l (a/l.block) site) (initSite site).count = _
    rw [ha,hCount]
    rfl
  obtain ⟨_,r,hRecord,_,hAction,_,_⟩ := init_record_of_consistent hMax.1
    (show X.MbInit (a,j) (obj.loc l cta) 1 from ⟨(initEvent l a site).pc,hExpected ▸ he⟩)
  have hMem := List.mem_of_getElem? hRecord
  have hMem' : r ∈ X.objects (initObject l cta site) := hMem
  have hFirst := (activeObjectHistory hp hMax.1 site hMem').1
  rw [hCount] at hFirst
  exact ⟨hFirst,r,hMem,hAction⟩

private theorem queryReleaseWarp (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {spec : TcCommit.Spec}
    (he : X.get (g,j) = some ⟨(Mma.commitSite (Mma.queryReleaseSite 1)).pc,.tc (.commit spec)⟩) :
    warpIndex l g = 12 := by
  have hBody := roleBodyPcOfEvent hp hX he (show 173 < 2541 by decide)
    (show 2541 ∉ registerHintSites by decide)
  change roleBodyPc (warpIndex l g) 2541 at hBody
  rcases hBody with h | h
  · omega
  · split_ifs at h <;> omega

private theorem idleReleaseNoUpdatesOfNoWork (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} (obj : IdleReleaseObject)
    (hNoWork : ∀ {g j : Nat} {e : Event}, g < l.threads → warpIndex l g = 12 →
      g / l.block = cta → X.get (g,j) = some e → 2042 ≤ e.pc → e.pc < 2763 → False) {r : Record Ref}
    (hr : r ∈ X.objects (obj.loc l cta)) : ¬ CounterUpdate r.action := by
  intro hUpdate
  cases obj with
  | cache slot =>
    let owner := cta*l.block
    have hb : 0 < l.block := by rw [hp.block]; decide
    have hOwner : owner/l.block = cta := Nat.mul_div_cancel cta hb
    have hr' : r ∈ X.objects (Thread.Mma.Observation.emptyObject l owner slot) := by
      rw [← IdleReleaseObject.cacheLoc, hOwner]
      exact hr
    obtain ⟨g,j,rank,hId⟩ := Thread.Mma.emptyUpdateSource hp hX hr' hUpdate
    obtain ⟨form,spec,he,hTarget⟩ := Thread.Mma.releaseOfEmptyNotification hp hX hr' hId
    have he' : X.Commit (g,j) spec := ⟨_,he⟩
    have hCta : cta = g/l.block := by
      have h := actualCommitTargetOwner hp hX he' hTarget
      change owner/l.block = g/l.block at h
      rwa [hOwner] at h
    have hw := Thread.Mma.ReleaseIssue.issuerWarp hp hX he
    have hg := Step.CtaBar.thread_lt_of_get hX he
    have hSites : ∀ f : Thread.Mma.ReleaseForm,
        2042 ≤ (Mma.commitSite (Mma.releaseCommitSite (Thread.Mma.releaseIndex f))).pc ∧
        (Mma.commitSite (Mma.releaseCommitSite (Thread.Mma.releaseIndex f))).pc < 2763 := by
      intro f
      cases f <;> decide
    exact hNoWork hg hw hCta.symm he (hSites form).1 (hSites form).2
  | secondQuery =>
    obtain ⟨g,j,_,_,_,he,hCta,_,_⟩ := queryEmptyUpdateAt hp hX 1 hr hUpdate
    exact hNoWork (Step.CtaBar.thread_lt_of_get hX he) (queryReleaseWarp hp hX he) hCta
      he (show 2042 ≤ 2541 by decide) (show 2541 < 2763 by decide)

/-- Every idle CTA leaves the loader's release objects without a work update. -/
theorem idleReleaseNoUpdatesForBatches (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat} (obj : IdleReleaseObject)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ cta) {r : Record Ref}
    (hr : r ∈ X.objects (obj.loc l cta)) : ¬ CounterUpdate r.action := by
  apply idleReleaseNoUpdatesOfNoWork hp hMax.1 obj ?_ hr
  intro g j e hg hw hCta he hLo hHi
  exact Mma.idleMmaNoTileWorkEvent hp hMax hg hw hCuQ (hCta.symm ▸ hIdle) he hLo hHi

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
