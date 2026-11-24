-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpCount
public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeCommit
public import Kernels.InklingRelDecode.Proof.Protocol.RingKvSlot
public import Lemmas.Flow.ElectLead

@[expose] public section

/-!
# The events on the KV ring's barriers, by thread

Which thread issues each event on `kv_ready s` and `kv_empty s` of a CTA, from the thread's states
and the event shapes:

* `arrive_kvReady`: an arrival on `kv_ready s` is the prologue's (a default-partition state) or the
  loader's, at its `arrive` site, by lane 0 of warp 6 (`ldThread`), 65536 bytes, count 1;
* `copy_kvReady`: a tensor copy completing on `kv_ready s` is the prologue's or a loader state's at
  a copy site; each copies one `(64, 64)` bf16 box, 8192 bytes; the loader's copying thread led
  its elections and is the thread `cpThread` (one lane of warp 6 leads every election);
* `commit_kvEmpty`: a commit whose target is `kv_empty s` is the MMA lane's at `pvCommit1`; that
  thread issued an MMA, so it is the CTA's committing lane of any `Sr.Lane`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty kvCopySpec)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Bytes -/

/-- A copy of the `kv_rows` map moves one `(64, 64)` bf16 box: 8192 bytes. -/
theorem kvCopy_bytes (Q : Params) (cta col row dst : Nat) (bar : Loc) :
    TensorTransfer.bytes (kvCopySpec Q cta col row dst bar).descriptor = Ring.Kv.copyBytes := by
  simp [kvCopySpec, TensorTransfer.bytes, mapKv, TensorTile.count, TensorTile.step,
    TensorTile.rows, TensorTile.rowsOf, TensorDescriptor.Format.bytes]

/-! ### The loader's threads -/

/-- Lane 0 of warp 6 of CTA `c`: the loader's arriving thread. -/
def ldThread (L : Launch) (c : Nat) : Nat := c * L.block + 192

open Classical in
/-- The thread of warp 6 of CTA `c` that led its elections, if one elected: the loader's copying
thread. -/
def cpThread (L : Launch) (X : Execution) (c : Nat) : Nat :=
  if h : ∃ h', SameWarp L (ldThread L c) h' ∧ ElectLead L h' (X.tr h') ∧
      ∃ ld, Elected (X.tr h') ld then Classical.choose h
  else ldThread L c

theorem ldThread_props (hb : L.block = 256) {c : Nat} (hc : c < L.grid) :
    ldThread L c < L.threads ∧ ldThread L c / L.block = c ∧ ldThread L c % L.block = 192 := by
  have hth : L.threads = L.grid * L.block := rfl
  unfold ldThread
  rw [hth, hb]
  refine ⟨by nlinarith, by omega, by omega⟩

theorem cpThread_props (hb : L.block = 256) {c : Nat} (hc : c < L.grid) :
    cpThread L X c < L.threads ∧ cpThread L X c / L.block = c ∧
      cpThread L X c % L.block / 32 = 6 := by
  obtain ⟨h1, h2, h3⟩ := ldThread_props hb hc
  unfold cpThread
  split
  · rename_i h
    obtain ⟨⟨⟨-, ha, hcta⟩, hw⟩, -⟩ := Classical.choose_spec h
    exact ⟨ha, by omega, by omega⟩
  · exact ⟨h1, h2, by omega⟩

/-- **The copying thread is the one that led and elected.** -/
theorem cpThread_eq (hX : Consistent L kernel asms mem0 X) {c h ld : Nat}
    (hw : SameWarp L (ldThread L c) h) (hl : ElectLead L h (X.tr h)) (he : Elected (X.tr h) ld) :
    cpThread L X c = h := by
  have hex : ∃ h', SameWarp L (ldThread L c) h' ∧ ElectLead L h' (X.tr h') ∧
      ∃ ld, Elected (X.tr h') ld := ⟨h, hw, hl, ld, he⟩
  unfold cpThread
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hw', hl', ld', he'⟩ := Classical.choose_spec hex
  have hw2 : SameWarp L (Classical.choose hex) h := by
    obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hw'
    obtain ⟨⟨b1, b2, b3⟩, b4⟩ := hw
    exact ⟨⟨a2, b2, by omega⟩, by omega⟩
  exact electLead_unique hX.elect hw2 (electMask_full hX _) (electMask_full hX h) he' he hl' hl

/-! ### Elections before the copy sites -/

theorem next_into_cp {d0 d : Loader.D} {e : Event} (hn : Loader.next L g d0 e = some (some d))
    (hs : Ring.Ld.isCp d.site = true) :
    (∃ mask inst, e.kind = .elect mask inst (laneOf L g)) ∨ Ring.Ld.isCp d0.site = true := by
  unfold Loader.next Loader.readI Loader.readN at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn
       subst hn
       (try rcases Loader.afterIter_site d0 with h | h) <;> simp_all [Ring.Ld.isCp])

/-- **A loader thread at a copy site has an election that returned its lane**, so it led every
election of its trace. -/
theorem copy_lead (hX : Consistent L kernel asms mem0 X) :
    ∀ (k : Nat) {d : Loader.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.loader d P))) → Ring.Ld.isCp d.site = true →
      Elected (X.tr g) (laneOf L g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hcp
    have hs0 : d.site ≠ .setMaxDec := by intro h; rw [h] at hcp; cases hcp
    obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ := loader_state_pred_adj hX hk hσ hs0
    rcases next_into_cp hn hcp with ⟨mask, inst, hk'⟩ | hcp0
    · exact ⟨e, List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he), mask, inst, hk'⟩
    · exact ih k0 (by omega) (by omega) hσ0 hcp0

/-! ### The events on `kv_ready` and `kv_empty` -/

/-- A loader thread is a thread of warp 6. -/
theorem loader_warp (hW : RoleWarps Q L X) {k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) : g % L.block / 32 = 6 := by
  have h := roleWarp_inv hW k _ hk hσ
  simpa [RoleWarp, roleWarp] using h

/-- **An arrival on `kv_ready s` of CTA `c`** is the prologue's (a default-partition state) or the
loader's at its `arrive` site, by lane 0 of warp 6 of the CTA; it expects 65536 bytes, count 1. -/
theorem arrive_kvReady (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc c s tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (hs : s < 3) (he : X.get (g, k) = some ⟨pc, .arrive (kvReady L c s) tx cnt rel sc⟩) :
    tx = Ring.Kv.txBytes ∧ cnt = 1 ∧ g / L.block = c ∧
      ((∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d)))) ∨
        ∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
          d.site = .arrive ∧ g = ldThread L c) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
    ⟨d, hσ, j, hj, -, hev⟩ | ⟨d, hσ, -, -, hev⟩ | ⟨d, P, hσ, hs', hsh⟩
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, hl, htx, hcnt, -⟩ := hev
    simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, EvD.Bar.loc, EvD.kvReadyOf, EvD.Bar.off,
      Loc.mk.injEq] at hl
    exact ⟨htx, hcnt, by omega, .inl ⟨d, hσ⟩⟩
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, EvD.Bar.loc, EvD.pReadyOf, EvD.Bar.off,
      Loc.mk.injEq] at hl
    omega
  · have hsh' := hsh
    unfold EvW.LdShape at hsh'
    rw [hs'] at hsh'
    simp only [Event.mk.injEq, Kind.arrive.injEq] at hsh'
    obtain ⟨-, hl, htx, hcnt, -⟩ := hsh'
    simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, Loc.mk.injEq] at hl
    obtain ⟨hI, -, -⟩ := loader_inv_at hX hf hk hσ
    have hln := hI.ln
    rw [hI.lane hs'] at hln
    have hl0 : laneOf L g = 0 := by simpa using hln.symm
    have hw := loader_warp hf.roleWarp hk.le hσ
    have hb := hpre.block
    unfold laneOf at hl0
    refine ⟨htx, hcnt, by omega, .inr ⟨d, P, hσ, hs', ?_⟩⟩
    unfold ldThread
    rw [hb] at hw hl0 ⊢
    have := Nat.div_add_mod g 256
    rw [hb] at hl
    omega

/-- **A tensor copy completing on `kv_ready s` of CTA `c`** is the prologue's (a default-partition
state) or a loader state's at a copy site, of a thread of the CTA; it moves 8192 bytes. -/
theorem copy_kvReady (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc a c s : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = kvReady L c s) :
    TensorTransfer.bytes sp.descriptor = Ring.Kv.copyBytes ∧ g / L.block = c ∧
      ((∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d)))) ∨
        ∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
          Ring.Ld.isCp d.site = true) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d, hσ, i, hi, hs', -⟩ | ⟨d, P, hσ, hsh⟩
  · obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
    obtain ⟨-, tm, -, hpro⟩ := hf.reach hg hσ
    have h := ProA.ptc_event hpre hi hpro (fired_pro hF) hs'
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    refine ⟨kvCopy_bytes _ _ _ _ _ _, ?_, .inl ⟨d, hσ⟩⟩
    simp only [EvW.kvCopySpec, EvD.Bar.loc, kvReady, EvW.barLoc, Loc.mk.injEq] at hm
    exact hm.2.1
  · have hcp : Ring.Ld.isCp d.site = true := by
      unfold EvW.LdShape at hsh
      cases hst : d.site <;> rw [hst] at hsh <;> simp at hsh <;> rfl
    obtain ⟨b, -, hev⟩ := Ring.ldShape_cp hsh hcp
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    refine ⟨kvCopy_bytes _ _ _ _ _ _, ?_, .inr ⟨d, P, hσ, hcp⟩⟩
    simp only [EvW.ldCopy, EvW.kvCopySpec, kvReady, EvW.barLoc, Loc.mk.injEq] at hm
    exact hm.2.1

/-- **A commit notifying `kv_empty s` of CTA `c`** is a commit at rank 0 to the barrier itself, of a
thread of the CTA at `pvCommit1` that led its elections and issued an MMA before. -/
theorem commit_kvEmpty (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {i : EvId} {pc c s : Nat} {sp : TcCommit.Spec}
    {rank : Fin 16} (hs : s < 3) (he : X.get i = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp rank = some (kvEmpty L c s)) :
    rank.val = 0 ∧ sp.mbar = kvEmpty L c s ∧ i.1 / L.block = c ∧ i.1 < L.threads ∧
      ElectLead L i.1 (X.tr i.1) ∧ ∃ k', SO.IsMma X (i.1, k') := by
  obtain ⟨g, k⟩ := i
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (Or.inr ⟨sp, rfl⟩)
  have hsite : d.site = .pvCommit1 ∧ sp = EvW.commitSpec (g / L.block)
      (kvEmpty L (g / L.block) ((d.i - 1) % 3)) := by
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
         exact ⟨rfl, rfl⟩)
      | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
         obtain ⟨-, rfl⟩ := hsh
         obtain ⟨-, hl⟩ := Life.target_commitSpec ht
         simp [EvW.oFinal, EvW.sReady, kvEmpty, EvW.oDone, EvW.barLoc, EvW.oFinalOff,
           EvW.sReadyOff, EvW.kvEmptyOff, EvW.oDoneOff] at hl
         omega)
  obtain ⟨hs1, rfl⟩ := hsite
  obtain ⟨hr0, hl⟩ := Life.target_commitSpec ht
  simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, Loc.mk.injEq] at hl
  obtain ⟨-, hc, ha⟩ := hl
  obtain ⟨k0, e0, d0, hadj, -, he0, hσ0, hn⟩ :=
    mma_state_pred_adj hX hk hσ (by rw [hs1]; nofun)
  have h7 := next_into_pvCommit1 hn hs1
  obtain ⟨pc', dst, sp', acc, mask, hev⟩ := mma_issue_event hpre hX hf hg he0 hσ0 (.inr ⟨7, h7⟩)
  have hk0 : k0 < (X.tr g).length := by omega
  refine ⟨hr0, ?_, hc.symm, hg, lead_of_pv hX 7 (j := 7) rfl hk0 hσ0 h7,
    k0, dst, sp', acc, mask, pc', by rw [he0, hev]⟩
  simp only [EvW.commitSpec, kvEmpty, EvW.barLoc, EvW.kvEmptyOff, Loc.mk.injEq]
  exact ⟨trivial, hc.symm, by omega⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
