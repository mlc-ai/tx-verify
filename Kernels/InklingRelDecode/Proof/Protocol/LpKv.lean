-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpPre
public import Kernels.InklingRelDecode.Proof2.Safety.InitAll
public import Kernels.InklingRelDecode.Proof.Protocol.KvRecords
public import Kernels.InklingRelDecode.Proof.Safety.Static
public import Kernels.InklingRelDecode.Proof.Protocol.SrCoord

@[expose] public section

/-!
# The slots of the KV ring under `Ring.Kv.Hyp`

`kv_of`: for every launched CTA `c` and slot `s`, the slot `Ring.Kv.Slot` of the barriers
`kv_ready s`, `kv_empty s` with

* `ap` lane 0 of warp 6 (`ldThread`), `cp` the lane of warp 6 that leads its elections
  (`cpThread`), `cm` the committing MMA lane of the handshake package (`G.cm c`),
* `δ = 1` exactly when the prologue preloads the slot (`s < num_pre`), and the prologue's arrival
  and copies `pArr`, `pCp` of `PreSlot`,

satisfies `Ring.Kv.Hyp`. The record sources are the event classifications of `LpEvents`; the
budgets and parities are `LpCount`'s, from the threads' anchored runs; the initialization is
`Proof2.kv_initFirst`; a commit to `kv_empty` is by a thread that issued an MMA, so it is `G.cm c`
(`Sr.Lane.mma_thread`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Events that do not touch the ring -/

/-- No thread arrives on `kv_empty`. -/
theorem no_arrive_kvEmpty (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc c s tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (hs : s < 3) : X.get (g, k) ≠ some ⟨pc, .arrive (kvEmpty L c s) tx cnt rel sc⟩ := by
  intro he
  have hg : g < L.threads := Frame.lt_of_get hX he
  rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
    ⟨d, hσ, j, hj, -, hev⟩ | ⟨d, hσ, -, -, hev⟩ | ⟨d, P, hσ, hs', hsh⟩
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, EvD.Bar.loc, EvD.kvReadyOf, EvD.Bar.off,
      Loc.mk.injEq] at hl
    omega
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, EvD.Bar.loc, EvD.pReadyOf, EvD.Bar.off,
      Loc.mk.injEq] at hl
    omega
  · unfold EvW.LdShape at hsh
    rw [hs'] at hsh
    simp only [Event.mk.injEq, Kind.arrive.injEq] at hsh
    obtain ⟨-, hl, -⟩ := hsh
    simp only [kvEmpty, kvReady, EvW.barLoc, EvW.kvEmptyOff, EvW.kvReadyOff, Loc.mk.injEq] at hl
    omega

/-- No tensor copy completes on `kv_empty`. -/
theorem no_copy_kvEmpty (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc a c s : Nat} {sp : TensorCopy.Spec} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) : sp.mbar ≠ kvEmpty L c s := by
  intro hm
  have hg : g < L.threads := Frame.lt_of_get hX he
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d, hσ, i, hi, hs', a', s', hev, -, -, h3, -⟩ | ⟨d, P, hσ, hsh⟩
  · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    rw [h3] at hm
    simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, EvD.Bar.loc, EvD.kvReadyOf, EvD.Bar.off,
      Loc.mk.injEq] at hm
    omega
  · have hcp : Ring.Ld.isCp d.site = true := by
      unfold EvW.LdShape at hsh
      cases hst : d.site <;> rw [hst] at hsh <;> simp at hsh <;> rfl
    obtain ⟨b, -, hev⟩ := Ring.ldShape_cp hsh hcp
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    simp only [EvW.ldCopy, EvW.kvCopySpec, kvReady, kvEmpty, EvW.barLoc, EvW.kvReadyOff,
      EvW.kvEmptyOff, Loc.mk.injEq] at hm
    omega

/-- No commit notifies `kv_ready`. -/
theorem no_commit_kvReady (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {i : EvId} {pc c s : Nat} {sp : TcCommit.Spec}
    {rank : Fin 16} (hs : s < 3) (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    TcCommit.target sp rank ≠ some (kvReady L c s) := by
  intro ht
  obtain ⟨g, k⟩ := i
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (Or.inr ⟨sp, rfl⟩)
  unfold EvW.MmShape at hsh
  cases hst : d.site <;> rw [hst] at hsh
  all_goals first
    | (simp at hsh; done)
    | (unfold EvW.QkIssue at hsh
       obtain ⟨_, _, _, _, _, _, hev⟩ := hsh
       simp at hev)
    | (unfold EvW.PvIssue at hsh
       obtain ⟨_, _, _, _, hev⟩ := hsh
       simp at hev)
    | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
       obtain ⟨-, rfl⟩ := hsh
       obtain ⟨-, hl⟩ := Life.target_commitSpec ht
       simp [EvW.oFinal, EvW.sReady, kvEmpty, kvReady, EvW.oDone, EvW.barLoc, EvW.oFinalOff,
         EvW.sReadyOff, EvW.kvEmptyOff, EvW.kvReadyOff, EvW.oDoneOff] at hl
       omega)

/-! ### The slot -/

/-- The slot `s` of CTA `c`, with the committing lane `cm` and the prologue's events. -/
def slotOf (Q : Params) (L : Launch) (X : Execution) (c s cm : Nat) (pArr : EvId)
    (pCp : Fin 8 → EvId) : Ring.Kv.Slot :=
  ⟨kvReady L c s, kvEmpty L c s, ldThread L c, cpThread L X c, cm,
    if s < npOf Q L c then 1 else 0, pArr, pCp⟩

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
  (G : Sr.SrPkg L kernel asms mem0 X)
include hpre hX hf hR hp

/-- **A loader copy on `kv_ready s` is the copying thread's, within its budget.** -/
theorem loader_copy_src {c s k pc a : Nat} {sp : TensorCopy.Spec} {d : Loader.D}
    {P : Loader.Pro} (hs : s < 3) (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hm : sp.mbar = kvReady L c s) (hc : g / L.block = c)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hcp : Ring.Ld.isCp d.site = true) :
    g = cpThread L X c ∧ ((X.tr g).take k).countP (issuesTo (kvReady L c s)) + 1 ≤
      8 * okPolls (kvEmpty L c s) ((X.tr g).take k) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  have hel := copy_lead hX k hk hσ hcp
  have hlead := electLead_of_elected hX hel
  have hw := loader_warp hf.roleWarp hk.le hσ
  have hgr : c < L.grid := by
    have := ProA.grid_lt hg
    omega
  obtain ⟨h1, h2, h3⟩ := ldThread_props hpre.block hgr
  have hsw : SameWarp L (ldThread L c) g := ⟨⟨h1, hg, by omega⟩, by omega⟩
  refine ⟨(cpThread_eq hX hsw hlead hel).symm, ?_⟩
  subst hc
  exact copy_budget hpre hX hf hR hp hlead hσ hs he hm

/-- **The records of `kv_ready s`.** -/
theorem full_src {c s : Nat} (hs : s < 3) {pArr : EvId}
    {pCp : Fin 8 → EvId} (hP : PreSlot Q L X c s pArr pCp) (cm : Nat)
    (F : SO.Facts L X c (G.cm c) (G.p0 c)) :
    ∀ r ∈ X.objects (kvReady L c s),
      Ring.Kv.FullSource X (slotOf Q L X c s cm pArr pCp) r := by
  intro r hr
  have hδ : ∀ (h : s < npOf Q L c), (slotOf Q L X c s cm pArr pCp).δ = 1 := by
    intro h; simp [slotOf, h]
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact .init ha
  | inval _ he _ => exact (F.no_inval he).elim
  | @arrive g j pc tx cnt rel sc hid he ha =>
    obtain ⟨htx, hcnt, hgc, hcase⟩ := arrive_kvReady hpre hX hf hs he
    subst htx hcnt
    rcases hcase with ⟨d, hσ⟩ | ⟨d, P, hσ, hs', rfl⟩
    · obtain ⟨hpa, hnp⟩ := hP.arr he hσ
      rw [hpa] at hid he
      exact .preArrive (hδ hnp) hid he ha
    · refine .arrive hid he ha ?_
      have := arrive_budget hpre hX hf hR hp hσ hs (by rw [hgc]; exact he)
      rw [hgc] at this
      exact this
  | wait hid he ha => exact .poll hid he ha
  | increment _ he _ => exact (F.no_arriveOn he).elim
  | @tensor i pc a sp hid he hm ha =>
    obtain ⟨g, k⟩ := i
    obtain ⟨hb, hgc, hcase⟩ := copy_kvReady hpre hX hf he hm
    rw [hb] at ha
    rcases hcase with ⟨d, hσ⟩ | ⟨d, P, hσ, hcp⟩
    · obtain ⟨⟨i', hi'⟩, hnp⟩ := hP.cp he hm hσ
      rw [hi'] at hid he
      exact .preCopy (hδ hnp) hid he hm ha
    · obtain ⟨hcpg, hbud⟩ := loader_copy_src hpre hX hf hR hp hs he hm hgc hσ hcp
      subst hcpg
      exact .copy hid he hm ha hbud
  | arriveOn _ he _ _ _ => exact (F.no_arriveOn he).elim
  | bulk _ he _ _ _ => exact (F.no_bulk he).elim
  | commit _ he ht _ => exact (no_commit_kvReady hpre hX hf hs he ht).elim
  | clc _ he _ _ _ => exact (F.no_clc he).elim

omit hp in
/-- **The records of `kv_empty s`.** -/
theorem empty_src {c s : Nat} (hc : c < L.grid) (hs : s < 3) (pArr : EvId)
    (pCp : Fin 8 → EvId) (F : SO.Facts L X c (G.cm c) (G.p0 c)) :
    ∀ r ∈ X.objects (kvEmpty L c s),
      Ring.Kv.EmptySource X (slotOf Q L X c s (G.cm c) pArr pCp) r := by
  intro r hr
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact .init ha
  | inval _ he _ => exact (F.no_inval he).elim
  | arrive _ he _ => exact (no_arrive_kvEmpty hpre hX hf hs he).elim
  | wait hid he ha => exact .poll hid he ha
  | increment _ he _ => exact (F.no_arriveOn he).elim
  | tensor _ he hm _ => exact (no_copy_kvEmpty hpre hX hf hs he hm).elim
  | arriveOn _ he _ _ _ => exact (F.no_arriveOn he).elim
  | bulk _ he _ _ _ => exact (F.no_bulk he).elim
  | @commit i pc sp rank hid he ht ha =>
    obtain ⟨hr0, hm, hgc, -, -, k', hmma⟩ := commit_kvEmpty hpre hX hf hs he ht
    have hcm : i.1 = G.cm c := (G.lane c hc).mma_thread (x := (i.1, k')) hmma hgc
    obtain ⟨g, k⟩ := i
    simp only at hcm hgc hr0
    subst hcm
    have hrk : rank = Ring.Kv.rank0 := Fin.ext hr0
    subst hrk
    refine .notify hid he hm ht ha ?_
    have := notify_budget hpre hX hf hR hs he (by rw [hgc]; exact hm)
    rw [hgc] at this
    exact this
  | clc _ he _ _ _ => exact (F.no_clc he).elim

/-- **The slot `s` of CTA `c` satisfies `Ring.Kv.Hyp`**, with the committing MMA lane of the
handshake package and the prologue's events of `PreSlot`. -/
theorem slot_hyp {c : Nat} (hc : c < L.grid) {s : Nat} (hs : s < 3) {pArr : EvId}
    {pCp : Fin 8 → EvId} (hP : PreSlot Q L X c s pArr pCp) :
    Ring.Kv.Hyp L kernel asms X (slotOf Q L X c s (G.cm c) pArr pCp) := by
  have F : SO.Facts L X c (G.cm c) (G.p0 c) := (G.ctx c hc).facts
  have hcm := (G.lane c hc).cm_ok
  obtain ⟨ha1, ha2, ha3⟩ := ldThread_props hpre.block hc
  obtain ⟨hc1, hc2, hc3⟩ := cpThread_props (X := X) hpre.block hc
  have hinit := Proof2.kv_initFirst hpre hX c hs
  have hth : L.threads = L.grid * L.block := rfl
  refine
    { δ_le := by simp only [slotOf]; split <;> omega
      full_src := full_src hpre hX hf hR hp G hs hP _ F
      empty_src := empty_src hpre hX hf hR G hc hs pArr pCp F
      full_init := hinit.1
      empty_init := hinit.2
      full_noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => F.no_inval he) _
      empty_noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => F.no_inval he) _
      full_parity := fun he => full_parity hpre hX hf hR hs he
      empty_parity := fun {g k pc p acq sc} he => ?_
      spins := fun w pc m q acq sc he => Safety.poll_spins hX he
      full_acq := fun he => by
        obtain ⟨-, -, -, -, -, -, -, h1, h2⟩ := poll_kvReady hpre hX hf hs he
        exact ⟨h1, h2⟩
      empty_acq := fun he => by
        obtain ⟨-, -, -, -, -, -, h1, h2⟩ := poll_kvEmpty hpre hX hf hs he
        exact ⟨h1, h2⟩
      cta := fun a => ?_
      issue := fun {g k pc al sp} he hm => ?_
      pre_cta := fun _ i => ?_
      pre_ne := fun _ => ?_
      pre_inj := fun _ => hP.cp_inj }
  · obtain ⟨-, -, -, -, hgc, -⟩ := poll_kvEmpty hpre hX hf hs he
    have h := empty_parity hpre hX hf hR hp hs he
    rw [← npOf_eq, hgc] at h
    rw [h]
    simp only [slotOf]
    split <;> simp
  · have hb := hpre.block
    by_cases ha : a = 0
    · subst ha
      show ldThread L c < L.threads ∧ G.cm c < L.threads ∧ ldThread L c / L.block = G.cm c / L.block
      exact ⟨ha1, hcm.1, by omega⟩
    · have : (slotOf Q L X c s (G.cm c) pArr pCp).prod a = cpThread L X c := by
        simp [Ring.Kv.Slot.prod, slotOf, ha]
      rw [this]
      show cpThread L X c < L.threads ∧ G.cm c < L.threads ∧
        cpThread L X c / L.block = G.cm c / L.block
      exact ⟨hc1, hcm.1, by omega⟩
  · obtain ⟨-, hgc, hcase⟩ := copy_kvReady hpre hX hf he hm
    rcases hcase with ⟨d, hσ⟩ | ⟨d, P, hσ, hcp⟩
    · obtain ⟨⟨i', hi'⟩, hnp⟩ := hP.cp he hm hσ
      exact .inr ⟨by simp [slotOf, hnp], i', hi'⟩
    · obtain ⟨hcpg, hbud⟩ := loader_copy_src hpre hX hf hR hp hs he hm hgc hσ hcp
      exact .inl ⟨hcpg, hbud⟩
  · obtain ⟨h1, -⟩ := hP.cp_thr i
    have hb := hpre.block
    have hlt : (pCp i).1 < L.threads := by
      rw [hth]
      exact (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
    show (pCp i).1 < L.threads ∧ G.cm c < L.threads ∧ (pCp i).1 / L.block = G.cm c / L.block
    exact ⟨hlt, hcm.1, by omega⟩
  · obtain ⟨-, h2⟩ := hP.arr_thr
    refine ⟨fun h => ?_, fun i h => ?_⟩
    · simp only [slotOf] at h
      rw [h] at h2
      omega
    · obtain ⟨-, h4⟩ := hP.cp_thr i
      simp only [slotOf] at h
      rw [h] at h4
      omega

/-- **Every slot of the KV ring is a `Ring.Kv.Slot` under `Ring.Kv.Hyp`**, whose consumer is the
committing MMA lane of the handshake package, given the prologue's events (`PreRing`). -/
theorem kv_of (hpr : PreRing Q L X) :
    ∀ cta < L.grid, ∀ s : Fin 3, ∃ S : Ring.Kv.Slot, S.full = kvReady L cta s ∧
      S.empty = kvEmpty L cta s ∧ S.cm = G.cm cta ∧ Ring.Kv.Hyp L kernel asms X S := by
  intro c hc s
  obtain ⟨pArr, pCp, hP⟩ := hpr c hc s s.isLt
  exact ⟨slotOf Q L X c s (G.cm c) pArr pCp, rfl, rfl, rfl,
    slot_hyp hpre hX hf hR hp G hc s.isLt hP⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
