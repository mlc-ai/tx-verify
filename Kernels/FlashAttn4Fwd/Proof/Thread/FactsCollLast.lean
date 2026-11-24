-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollLastPred
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid2Reg

@[expose] public section

/-! # `WarpCollFacts.last`

The `n`-th warp collective of a lane of warp `key` is at time `S key n` of the schedule
(`Cross.WarpSched`), so at the position `collPc (Work.n L) (S key n)` (`state_pc`). Its last
event is fired from the state before it, and never blocks unless that state's kind is blocking
(`fires_unblocking`); a machine steps from a blocking kind to a warp collective only in two
places (`pred_blocking`), each recognized from the warp and the time:

* the loader's first broadcast, the only loader warp collective at time `base`
  (`loader_base`), follows its `setmaxnreg`, the thread's first request with its warp's position
  and operands (`reg_request`);
* a softmax warp barrier, at the position of a warp barrier, follows the tile's second
  `tcgen05.wait::st` (`soft_pred`), a warp-collective `tcgen05` event other than a paired Tensor
  Memory operation. Before the barrier of tile `τ` of item `i` the thread has made
  `14 (n i + τ + 1)` warp-collective `tcgen05` events (`Softmax.Counts.tcColl`), so the
  `tcgen05.wait::st` is the one of ordinal `14 (n i + τ) + 13`; the barrier's time is in global
  slot `i (n + 1) + τ`, from which `tcOrd` computes that ordinal.

Every other last event never blocks. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Cross Sched Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Sched

/-- The position of a softmax warp barrier. -/
def WarpBarPc (pc : Nat) : Prop :=
  pc = (Softmax.Site.warpBar false).pc ∨ pc = (Softmax.Site.warpBar true).pc

instance (pc : Nat) : Decidable (WarpBarPc pc) := by unfold WarpBarPc; infer_instance

/-- The ordinal of the `tcgen05.wait::st` before the softmax warp barrier at time `τ`. -/
def tcOrd (n τ : Nat) : Nat :=
  14 * ((τ - base) / span - (τ - base) / span / (n + 1)) + 13

theorem tcOrd_at {n i s o : Nat} (hs : s ≤ n) (ho : o < span) :
    tcOrd n (slotTime n i s o) = 14 * (n * i + s) + 13 := by
  have h : slotTime n i s o - base = o + span * (i * (n + 1) + s) := by
    unfold slotTime gslot; omega
  have h1 : (o + span * (i * (n + 1) + s)) / span = i * (n + 1) + s := by
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt ho, Nat.zero_add]
  have h2 : (i * (n + 1) + s) / (n + 1) = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos n),
      Nat.div_eq_of_lt (Nat.lt_succ_of_le hs), Nat.zero_add]
  simp only [tcOrd, h, h1, h2]
  have : i * (n + 1) + s - i = n * i + s := by
    rw [Nat.mul_succ, Nat.mul_comm]; omega
  rw [this]

/-- No prologue or softmax warp collective but a warp barrier is at a warp barrier's
position. -/
theorem warpBar_of_pc {g : Nat} {d : ThreadD} (hk : nextKind d = .warp)
    (hw : (∃ p, d = .inl p) ∨ ∃ s, d = .inr (.softmax s))
    (hp : WarpBarPc ((code L g).pc d)) : ∃ s lp, d = .inr (.softmax s) ∧ s.site = .warpBar lp := by
  have he : ∀ e : Fin 14, ¬ WarpBarPc (Prologue.Site.elect e).pc := by decide +kernel
  rcases hw with ⟨⟨site⟩, rfl⟩ | ⟨s, rfl⟩
  · exfalso
    have hp' : WarpBarPc site.pc := hp
    cases site <;> simp only [nextKind, prologueKind, reduceCtorEq] at hk
    all_goals first | exact he _ hp' | exact absurd hp' (by decide +kernel)
  · refine ⟨s, ?_⟩
    have hp' : WarpBarPc s.site.pc := hp
    obtain ⟨site, i, t, w, m, l⟩ := s
    cases site <;> simp only [nextKind, softmaxKind, reduceCtorEq] at hk
    · exact ⟨_, rfl, rfl⟩
    · rename_i lp
      exfalso
      cases lp <;> exact absurd (show WarpBarPc (Softmax.Site.el _).pc from hp') (by decide +kernel)

end Sched

/-- **`WarpCollFacts.last`.** -/
theorem WarpCollFacts_last (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L) {S : Nat × Nat → Nat → Nat}
    (hs : WarpSched L X S) :
    ∃ R : Nat × Nat → Nat → Option ((Nat × Bool × Nat) ⊕ Nat),
      ∀ {g : Nat} {d : ThreadD}, g < L.threads → St L X g (X.tr g).length = some (some d) →
        nextKind d = .warp →
        match R (warpKey L g) ((X.tr g).countP Sched.isWarpColl) with
        | none => ∀ q, X.get (g, (X.tr g).length - 1) = some q → Sched.Unblocking q.kind
        | some (.inl (pc, inc, n)) => ∃ inst,
          X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ ∧
            SetMaxNReg.ordinal X (g, (X.tr g).length - 1) = 0
        | some (.inr k) => X.TcK (g, (X.tr g).length - 1) k ∧
          ∀ pc grp dst act, X.get (g, (X.tr g).length - 1) ≠
            some ⟨pc, .tc (.resource grp dst act)⟩ := by
  refine ⟨fun key n => if key.2 = 14 ∧ S key n = base then
      some (.inl (Safety.regPc key.2, (Safety.regOf key.2).1, (Safety.regOf key.2).2))
    else if key.2 < 8 ∧ WarpBarPc (collPc (Work.n L) (S key n)) then
      some (.inr (tcOrd (Work.n L) (S key n)))
    else none, ?_⟩
  intro g d hg hσ hk
  have hτ := hs.endAt hg hσ hk
  obtain ⟨hJ, hinv, hw⟩ := state_facts hpre hX ht hok hg le_rfl hσ
  have hpc : (code L g).pc d = collPc (Work.n L) (S (warpKey L g) ((X.tr g).countP
      Sched.isWarpColl)) :=
    by rw [state_pc hinv hk, hτ]
  have hkey : (warpKey L g).2 = warpOf L g := rfl
  -- a state other than the first has a last event, fired from the state before it
  have hlen : (∀ p, d ≠ .inl p) → 0 < (X.tr g).length := by
    intro hd
    by_contra h0
    have h0' : (X.tr g).length = 0 := by omega
    have := Frame.stateAt_zero (C := code L) (X := X) (g := g)
    rw [← h0'] at this
    change St L X g _ = _ at this
    rw [hσ] at this
    exact hd _ (Option.some.inj (Option.some.inj this))
  have hstep : (hl : 0 < (X.tr g).length) → ∃ d0 t ins u, (code L g).AtD d0 t ∧
      (code L g).inv d0 ∧ kernel.code[(code L g).pc d0]? = some ins ∧
      Fires ((code L g).pc d0) (eventTmpl asms L g t ins.op) (X.tr g)[(X.tr g).length - 1]
        (some u) ∧ (code L g).next d0 (X.tr g)[(X.tr g).length - 1] = some (some d) ∧
      X.get (g, (X.tr g).length - 1) = some (X.tr g)[(X.tr g).length - 1] ∧
      St L X g ((X.tr g).length - 1) = some (some d0) := by
    intro hl
    obtain ⟨d0, hσ0⟩ := Frame.stateAt_live (C := code L) ht hg hσ (Nat.sub_le _ 1)
    obtain ⟨t, ins, u, h⟩ := last_step hpre hX hok hg hσ hl hσ0
    exact ⟨d0, t, ins, u, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      List.getElem?_eq_getElem (show (X.tr g).length - 1 < (X.tr g).length by omega), hσ0⟩
  by_cases hA : warpOf L g = 14 ∧ S (warpKey L g) ((X.tr g).countP Sched.isWarpColl) = base
  · simp only [hkey, hA, and_self, ↓reduceIte]
    -- the state is the loader's first broadcast
    obtain ⟨l, rfl, hh, hi0⟩ : ∃ l, d = .inr (.loader l) ∧ l.site = .head ∧ l.i = 0 := by
      rcases role_cases hw with ⟨⟨p⟩, rfl⟩ | ⟨h15, -⟩ | ⟨-, l, rfl⟩ | ⟨h12, -⟩ | ⟨h13, -⟩ |
          ⟨h8, -⟩ | ⟨h8, h12, -⟩
      · have := Progress.Time.prologue_lt_reg p
        simp only [stateTime] at hτ
        rw [hA.2] at hτ
        simp only [regT, base] at this hτ
        omega
      · omega
      · exact ⟨l, rfl, Sched.loader_base hk (hτ.trans hA.2)⟩
      all_goals omega
    obtain ⟨d0, t, ins, u, hat, hinv0, hc0, hf, hn, hget, -⟩ := hstep (hlen (by simp))
    -- the state before is the loader's request
    have hreg : nextKind d0 = .reg := by
      rcases d0 with p | r
      · obtain ⟨p', hp'⟩ := Sched.pro_succ hn hk
        cases hp'
      obtain ⟨r', hr', hkr⟩ := code_next_inr hn
      cases r <;> cases r' <;> simp only [Role.kind, reduceCtorEq] at hkr <;>
        simp only [Sum.inr.injEq, reduceCtorEq] at hr'
      rename_i l0 l1
      simp only [Role.loader.injEq] at hr'
      subst hr'
      have hm := next_role (fun _ _ h => by cases h; rfl) hn
      simp [nextKind, Sched.loader_head_pred hm hh hi0, loaderKind]
    rcases tmpl_kind hat hc0 with ⟨f, hub⟩ | hm
    · exact absurd hub (hok g hg d0 t ins hat hinv0 hc0 f)
    rw [hreg] at hm
    obtain ⟨inc, n, t', hm⟩ := hm
    rw [hm] at hf
    obtain ⟨inst, he, -⟩ := hf
    rw [he] at hget
    obtain ⟨h0, hp, hrn⟩ := reg_request hpre hX ht hg hget
    refine ⟨inst, ?_, h0⟩
    rw [hA.1] at hp hrn
    rw [hget, hp, ← hrn]
  by_cases hB : warpOf L g < 8 ∧
      WarpBarPc (collPc (Work.n L) (S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)))
  · simp only [hkey, hA, hB, and_self, ↓reduceIte]
    -- the state is a softmax warp barrier
    obtain ⟨sd, lp, rfl, hsite⟩ := warpBar_of_pc hk (by
      rcases role_cases hw with ⟨p, rfl⟩ | ⟨h15, -⟩ | ⟨h14, -⟩ | ⟨h12, -⟩ | ⟨h13, -⟩ |
          ⟨-, s, rfl⟩ | ⟨h8, h12, -⟩
      · exact .inl ⟨p, rfl⟩
      · omega
      · omega
      · omega
      · omega
      · exact .inr ⟨s, rfl⟩
      · omega) (by rw [hpc]; exact hB.2)
    have hl := hlen (by simp)
    obtain ⟨d0, t, ins, u, hat, hinv0, hc0, hf, hn, hget, hσ0⟩ := hstep hl
    -- the state before is the tile's second `tcgen05.wait::st`
    have hwait : nextKind d0 = .tcStore := by
      rcases d0 with p | r
      · obtain ⟨p', hp'⟩ := Sched.pro_succ hn hk
        cases hp'
      obtain ⟨r', hr', hkr⟩ := code_next_inr hn
      cases r <;> cases r' <;> simp only [Role.kind, reduceCtorEq] at hkr <;>
        simp only [Sum.inr.injEq, reduceCtorEq] at hr'
      rename_i s0 s1
      simp only [Role.softmax.injEq] at hr'
      subst hr'
      have hm := next_role (fun _ _ h => by cases h; rfl) hn
      obtain ⟨lp', h0, -⟩ := Sched.soft_pred hm hk (.inr ⟨lp, hsite⟩)
      simp [nextKind, h0, softmaxKind]
    have hfk := fired_kind hpre hX hok hg hσ0 hget
    rw [hwait] at hfk
    have htc : isTcColl (X.tr g)[(X.tr g).length - 1] = true := by
      rw [hfk.2.1]; rfl
    have hnot : Tmem.Pair.isTmemOp (X.tr g)[(X.tr g).length - 1] = false := by
      rw [hfk.2.2.1]; rfl
    refine ⟨⟨⟨_, hget, htc⟩, ?_⟩, fun pc grp dst act he => ?_⟩
    · -- the ordinal, from the softmax counts at the barrier
      have hc : (X.tr g).countP isTcColl =
          ((X.tr g).take ((X.tr g).length - 1)).countP isTcColl + 1 := by
        have hsp := Sched.split_last (X := X) (g := g) hl
        conv_lhs => rw [hsp]
        rw [List.countP_append]
        simp [htc]
      have hcnt : (X.tr g).countP isTcColl = 14 * Softmax.trips L * sd.i + Softmax.tcPos sd := by
        have h := hJ
        rw [List.take_length] at h
        exact h.tcColl
      have hi : Softmax.Inv L g sd := hinv
      have hst : Softmax.stOf L g < 2 := by
        have := hi.warp; simp only [Softmax.stOf]; omega
      obtain ⟨site, i, tt, w, m, l⟩ := sd
      simp only at hsite
      subst hsite
      have hτ' := hτ
      simp only [stateTime, Progress.Time.softmax] at hτ'
      rw [← hτ']
      have hN : Softmax.trips L = Work.n L := rfl
      cases lp
      · simp only [softSlot, Bool.false_eq_true, ↓reduceIte] at hτ' ⊢
        rw [tcOrd_at (Nat.zero_le _) (by simp only [bandS, span]; omega)]
        simp only [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
          Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip] at hcnt
        simp at hcnt
        rw [hN, Nat.mul_assoc] at hcnt
        omega
      · have htr := hi.trip rfl
        simp only at htr
        simp only [softSlot, ↓reduceIte] at hτ' ⊢
        rw [tcOrd_at (by rw [← hN]; omega) (by simp only [bandS, span]; omega)]
        simp only [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
          Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip] at hcnt
        simp at hcnt
        rw [hN, Nat.mul_assoc] at hcnt
        omega
    · rw [hget] at he
      rw [Option.some.inj he] at hnot
      cases hnot
  · simp only [hkey, hA, hB, ↓reduceIte]
    intro q hq
    have hl : 0 < (X.tr g).length := by
      rcases Nat.eq_zero_or_pos (X.tr g).length with h0 | h0
      · have : X.tr g = [] := List.length_eq_zero_iff.mp h0
        simp [Execution.get, this] at hq
      · exact h0
    obtain ⟨d0, hσ0⟩ := Frame.stateAt_live (C := code L) ht hg hσ (Nat.sub_le _ 1)
    obtain ⟨t, ins, u, hat, hinv0, hc0, hf, hn⟩ := last_step hpre hX hok hg hσ hl hσ0
    have hget : X.get (g, (X.tr g).length - 1) = some (X.tr g)[(X.tr g).length - 1] :=
      List.getElem?_eq_getElem (show (X.tr g).length - 1 < (X.tr g).length by omega)
    rw [hget] at hq
    obtain rfl := Option.some.inj hq
    by_cases hb : Sched.Blocking (nextKind d0)
    · exfalso
      rcases pred_blocking hn hk hb with ⟨l, rfl, hh, hi0⟩ | ⟨sd, lp, rfl, hsite⟩
      · have hw14 : warpOf L g = 14 := by
          have := hw _ rfl
          simpa [Role.kind, RoleKind.Warp] using this
        refine hA ⟨hw14, ?_⟩
        rw [← hτ]
        obtain ⟨site, i, t, s, ph, qp⟩ := l
        simp only at hh hi0
        subst hh hi0
        simp [stateTime, Progress.Time.loader, loaderUse, slotTime, gslot]
      · have hw8 : warpOf L g < 8 := by
          have := hw _ rfl
          simpa [Role.kind, RoleKind.Warp] using this
        refine hB ⟨hw8, ?_⟩
        rw [← hpc]
        change WarpBarPc sd.site.pc
        rw [hsite]
        cases lp
        · exact .inl rfl
        · exact .inr rfl
    rcases tmpl_kind hat hc0 with ⟨f, hub⟩ | hm
    · exact absurd hub (hok g hg d0 t ins hat hinv0 hc0 f)
    exact fires_unblocking hm hf hb

end
end PTX.Kernels.FlashAttn4Fwd.Proof
