-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsMma
public import Kernels.InklingRelDecode.Proof2.Safety.InitAll

@[expose] public section

/-!
# The commits of the kernel and the record sources of the handshake barriers (`SO.Facts`)

* `commit_state`: a commit fires at one of the MMA role's four commit sites, with the barrier the
  site names (`s_ready`, `kv_empty`, `o_done`, `o_final` of the thread's CTA);
* `commit_lead`: a commit to `s_ready`, `o_done` or `o_final` is by the elected lane of its CTA's
  MMA warp (the QK commit after QK MMA 7, the second PV commit after PV MMA 7, the `o_final`
  commit after the election `finElect` that returned the thread's lane);
* `facts_of`: `SO.Facts L X c (cmOf L X c) (p0Of L c)` for every launched CTA, with the parities of
  `p_ready`, `s_ready` and `o_final` polls as premises (`HsParity` proves them).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal kvReady kvEmpty commitSpec)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma below2 CommitBar PBar)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The barrier locations unfolded to their CTA and offset. -/
macro "hs_loc" h:ident : tactic =>
  `(tactic| (simp only [EvW.sReady, EvW.pReady, EvW.oDone, EvW.oFinal, EvW.kvReady,
      EvW.kvEmpty, barLoc_eq, EvW.sReadyOff, EvW.pReadyOff, EvW.oDoneOff, EvW.oFinalOff,
      EvW.kvReadyOff, EvW.kvEmptyOff, EvD.Bar.loc, EvD.kvReadyOf, EvD.Bar.off, EvW.barLoc,
      Loc.mk.injEq, true_and] at $h:ident <;> omega))

/-- **A commit fires at a commit site of the MMA role**, notifying the barrier the site names. -/
theorem commit_state (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      ((d.site = .qkCommit ∧ sp = commitSpec (g / L.block) (sReady L (g / L.block) (d.i % 2))) ∨
        (d.site = .pvCommit1 ∧
          sp = commitSpec (g / L.block) (kvEmpty L (g / L.block) ((d.i - 1) % 3))) ∨
        (d.site = .pvCommit2 ∧ sp = commitSpec (g / L.block) (oDone L (g / L.block))) ∨
        (d.site = .finCommit ∧ sp = commitSpec (g / L.block) (oFinal L (g / L.block)))) := by
  have hg : g < L.threads := event_thread_lt hX he
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (.inr ⟨sp, rfl⟩)
  refine ⟨d, P, hσ, ?_⟩
  unfold EvW.MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
       obtain ⟨-, rfl⟩ := hsh
       simp)
    | (exfalso; simp [EvW.QkIssue, EvW.PvIssue] at hsh)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into the `o_final` commit: from the election `finElect` that returned the lane. -/
theorem next_finCommit {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .finCommit) :
    d0.site = .finElect ∧ ∃ mk inst ld, e.kind = .elect mk inst ld ∧ laneOf L g = ld := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hs; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp only at hs
       split at hs
       · rename_i hl
         exact ⟨by assumption, _, _, _, by assumption, hl⟩
       · cases hs)

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The `o_final` commit is by an elected lane.** -/
theorem fin_lead {k : Nat} {d : Mma.D} {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .finCommit)
    : LeadOf L X (g / L.block) g := by
  obtain ⟨k0, e, d0, hadj, hg, he, hσ0, hn⟩ := mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
  obtain ⟨hs0, mk, inst, ld, hek, hld⟩ := next_finCommit hn hs
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ0 (by simp [ExitState])
  obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
  have hsh := EvW.mma_shape hpre hg ⟨t', ⟨ha, hi.2⟩, hf'⟩
  unfold EvW.MmShape at hsh
  rw [hs0] at hsh
  obtain ⟨inst', ld', rfl⟩ := hsh
  simp only [Kind.elect.injEq] at hek
  obtain ⟨-, -, rfl⟩ := hek
  have h7 : Worker.warpOf L g = 7 := by
    simpa [RoleWarp, Ledger.roleWarp, Worker.warpOf] using
      roleWarp_inv hf.roleWarp k0 _ (by omega) hσ0
  refine ⟨⟨hg, rfl, ?_⟩, k0, Mma.Site.finElect.pc, inst', ?_⟩
  · unfold Worker.warpOf at h7
    exact h7
  · rw [hld]
    exact he

/-- **A commit to `s_ready`, `o_done` or `o_final` is by the elected lane of its CTA.** -/
theorem commit_lead {k pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (hne : ∀ s < 3, sp ≠ commitSpec (g / L.block) (kvEmpty L (g / L.block) s)) :
    LeadOf L X (g / L.block) g := by
  have hg : g < L.threads := event_thread_lt hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, h⟩ := commit_state hpre hX hf he
  rcases h with ⟨hs, -⟩ | ⟨-, hsp⟩ | ⟨hs, -⟩ | ⟨hs, -⟩
  · obtain ⟨k', d', hk', hσ', hs', -, -, -, pc', dst, sp', acc, mask, he'⟩ :=
      exists_qk7 hpre hX hf hk hσ hs
    exact mma_lead hpre hX hf (x := (g, k')) ⟨dst, sp', acc, mask, pc', he'⟩
  · exact absurd hsp (hne _ (Nat.mod_lt _ (by omega)))
  · obtain ⟨-, k', d', d1, hk', hσ', hs', -, -, -, -, -, pc', dst, sp', acc, mask, he'⟩ :=
      exists_pv7_commit2 hpre hX hf hk hσ hs
    exact mma_lead hpre hX hf (x := (g, k')) ⟨dst, sp', acc, mask, pc', he'⟩
  · exact fin_lead hpre hX hf hk hσ hs

/-! ### The fields of `SO.Facts` -/

/-- **A tensor copy completes on a `kv_ready` barrier of its thread's CTA.** -/
theorem tensor_mbar {k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    ∃ s < 3, sp.mbar = kvReady L (g / L.block) s := by
  have hg : g < L.threads := event_thread_lt hX he
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d, -, i, -, -, a', s', hev, -, -, hm, -⟩ | ⟨d, P, -, hsh⟩
  · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    refine ⟨i / 4 % 3, Nat.mod_lt _ (by omega), ?_⟩
    rw [hm]
    rfl
  · obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
    cases site <;> simp only [EvW.LdShape] at hsh
    all_goals first
      | (obtain ⟨b, -, hev⟩ := hsh
         simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
         obtain ⟨-, -, rfl⟩ := hev
         exact ⟨_, Nat.mod_lt _ (by omega), rfl⟩)
      | (obtain ⟨_, _, hev, -⟩ := hsh; cases hev)
      | (obtain ⟨_, _, hev⟩ := hsh; cases hev)
      | (obtain ⟨_, hev⟩ := hsh; cases hev)
      | cases hsh

/-- **An arrival is on `kv_ready` or, by thread 0 of the CTA, on `p_ready`.** -/
theorem arrive_loc {k pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩) :
    (∃ s < 3, m = kvReady L (g / L.block) s) ∨
      (∃ b < 2, m = pReady L (g / L.block) b ∧ g % L.block = 0 ∧ tx = 0 ∧ cnt = 1 ∧
        rel = true) := by
  have hg : g < L.threads := event_thread_lt hX he
  rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
    ⟨d, -, j, hj, -, hev⟩ | ⟨d, -, -, h0, hev⟩ | ⟨d, P, -, hs, hsh⟩
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, rfl, -⟩ := hev
    left
    refine ⟨j % 3, Nat.mod_lt _ (by omega), rfl⟩
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, rfl, rfl, rfl, rfl, -⟩ := hev
    right
    exact ⟨d.i % 2, Nat.mod_lt _ (by omega), rfl, h0, rfl, rfl, rfl⟩
  · unfold EvW.LdShape at hsh
    rw [hs] at hsh
    simp only [Event.mk.injEq, Kind.arrive.injEq] at hsh
    obtain ⟨-, rfl, -⟩ := hsh
    exact .inl ⟨_, Nat.mod_lt _ (by omega), rfl⟩

/-- The target of a commit of the kernel: the barrier its site names, in the thread's CTA. -/
theorem commit_target {k pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (ht : TcCommit.target sp r = some m) :
    sp.mbar = m ∧
      ((∃ b < 2, m = sReady L (g / L.block) b) ∨ (∃ s < 3, m = kvEmpty L (g / L.block) s) ∨
        m = oDone L (g / L.block) ∨ m = oFinal L (g / L.block)) := by
  obtain ⟨d, P, -, h⟩ := commit_state hpre hX hf he
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    obtain ⟨-, rfl⟩ := Life.target_commitSpec ht
  · exact ⟨rfl, .inl ⟨_, Nat.mod_lt _ (by omega), rfl⟩⟩
  · exact ⟨rfl, .inr (.inl ⟨_, Nat.mod_lt _ (by omega), rfl⟩)⟩
  · exact ⟨rfl, .inr (.inr (.inl rfl))⟩
  · exact ⟨rfl, .inr (.inr (.inr rfl))⟩

/-- **`SO.Facts`** of a launched CTA, given the parities of the polls of `s_ready`, `p_ready` and
`o_final`. -/
theorem facts_of {c : Nat}
    (hs : ∀ {g k pc p b : Nat} {acq : Bool} {sc : MbarScope}, b < 2 →
      X.get (g, k) = some ⟨pc, .wait (sReady L c b) p true acq sc⟩ →
        p % 2 = (okPolls (sReady L c b) ((X.tr g).take k) + 0) % 2)
    (hp : ∀ {g k pc p b : Nat} {acq : Bool} {sc : MbarScope}, b < 2 →
      X.get (g, k) = some ⟨pc, .wait (pReady L c b) p true acq sc⟩ →
        p % 2 = (okPolls (pReady L c b) ((X.tr g).take k) + 0) % 2)
    (hfp : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (g, k) = some ⟨pc, .wait (oFinal L c) p true acq sc⟩ →
        p % 2 = (okPolls (oFinal L c) ((X.tr g).take k) + 0) % 2) :
    SO.Facts L X c (cmOf L X c) (p0Of L c) where
  no_bulk := no_copy hX
  no_clc := no_clc hX
  no_inval := Safety.no_inval hX
  no_arriveOn := Safety.no_asyncArrive hX
  no_tensor := by
    intro i pc a sp he
    obtain ⟨g, k⟩ := i
    obtain ⟨s, hs3, hm⟩ := tensor_mbar hpre hX hf he
    rw [hm]
    refine ⟨?_, ?_⟩
    · rintro (⟨b, hb, h⟩ | h | h) <;> hs_loc h
    · rintro ⟨b, hb, h⟩
      hs_loc h
  commit_only := by
    intro i pc sp r m he ht hcb
    obtain ⟨g, k⟩ := i
    obtain ⟨hsp, hm⟩ := commit_target hpre hX hf he ht
    have hgc : g / L.block = c := by
      rcases hcb with ⟨b, hb, rfl⟩ | rfl | rfl <;>
        rcases hm with ⟨b', hb', h⟩ | ⟨s, hs3, h⟩ | h | h <;> hs_loc h
    have hne : ∀ s < 3, sp ≠ commitSpec (g / L.block) (kvEmpty L (g / L.block) s) := by
      intro s hs3 hs'
      rw [hs'] at hsp
      simp only [commitSpec] at hsp
      rw [← hsp] at hcb
      rcases hcb with ⟨b, hb, h⟩ | h | h <;> hs_loc h
    have hl := commit_lead hpre hX hf he hne
    rw [hgc] at hl
    exact ⟨(cm_eq hX hl).symm, hsp⟩
  no_commit_p := by
    intro i pc sp r m he ht hpb
    obtain ⟨g, k⟩ := i
    obtain ⟨b, hb, rfl⟩ := hpb
    obtain ⟨-, hm⟩ := commit_target hpre hX hf he ht
    rcases hm with ⟨b', hb', h⟩ | ⟨s, hs3, h⟩ | h | h <;> hs_loc h
  no_arrive_commit := by
    intro g i pc tx cnt m rel sc hcb he
    rcases arrive_loc hpre hX hf he with ⟨s, hs3, rfl⟩ | ⟨b, hb, rfl, -⟩ <;>
      rcases hcb with ⟨b', hb', h⟩ | h | h <;> hs_loc h
  p_arrive := by
    intro g i pc tx cnt m rel sc hpb he
    obtain ⟨b, hb, rfl⟩ := hpb
    rcases arrive_loc hpre hX hf he with ⟨s, hs3, h⟩ | ⟨b', hb', h, h0, rfl, rfl, rfl⟩
    · hs_loc h
    · have hgc : g / L.block = c := by hs_loc h
      refine ⟨?_, rfl, rfl, rfl⟩
      unfold p0Of
      rw [← hgc]
      have := Nat.div_add_mod g L.block
      rw [h0] at this
      rw [Nat.mul_comm]
      omega
  init := fun hm => by
    rcases hm with (⟨b, hb, rfl⟩ | rfl | rfl) | ⟨b, hb, rfl⟩
    · exact Proof2.all_initFirst hpre hX c (.sReady ⟨b, hb⟩)
    · exact Proof2.all_initFirst hpre hX c .oDone
    · exact Proof2.all_initFirst hpre hX c .oFinal
    · exact Proof2.all_initFirst hpre hX c (.pReady ⟨b, hb⟩)
  s_parity := hs
  p_parity := hp
  f_parity := hfp

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
