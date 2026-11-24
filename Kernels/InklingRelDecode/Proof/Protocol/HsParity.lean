-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsFacts

@[expose] public section

/-!
# The parities of the handshake polls

A successful poll of `s_ready b`, `p_ready b`, `o_done` or `o_final` waits for the parity of the
number of successful polls of the same barrier its thread made before it:

* `s_ready b`, `o_done`: at the softmax sites `waitS`, `waitO`, with the counts of `Rd.sm_cnt`;
* `p_ready b`: at the MMA site `pWait`, with the counts of `mma_cnt`;
* `o_final`: at the epilogue's `wait`, the thread's first successful poll of it (`epi_cnt`: the
  count is `SO.epiPolled` at an epilogue state and 0 before the epilogue).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The parity of a successful poll of `s_ready b`.** -/
theorem s_parity (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c g k pc p b : Nat} {acq : Bool} {sc : MbarScope}
    (hb : b < 2) (he : X.get (g, k) = some ⟨pc, .wait (sReady L c b) p true acq sc⟩) :
    p % 2 = (okPolls (sReady L c b) ((X.tr g).take k) + 0) % 2 := by
  have hg : g < L.threads := event_thread_lt hX he
  have hk : k < (X.tr g).length := len_of_get he
  rcases (poll_class hpre hX hf he).2.2 with
    ⟨d, hσ, hs, hm, hp⟩ | ⟨d, -, -, hm, -⟩ | ⟨d, P', -, -, hm⟩ | ⟨d, P', -, -, hm⟩ |
    ⟨d, P', -, -, hm, -⟩ | ⟨d, -, -, hm, -⟩
  rotate_left 1
  all_goals try hs_loc hm
  have hm' := hm
  simp only [EvW.sReady, barLoc_eq, EvW.sReadyOff] at hm'
  obtain ⟨hc, hbi⟩ := hm'
  subst hc
  have hb' : d.i % 2 = b := by omega
  have hcnt := ((Rd.sm_cnt hpre hX hf hg k hk.le _ hσ).2 d rfl).s b hb
  rw [hcnt, hp]
  simp only [SO.smPolled, hs, below2]
  omega

/-- **The parity of a successful poll of `p_ready b`.** -/
theorem p_parity (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {c g k pc p b : Nat} {acq : Bool}
    {sc : MbarScope} (hb : b < 2)
    (he : X.get (g, k) = some ⟨pc, .wait (pReady L c b) p true acq sc⟩) :
    p % 2 = (okPolls (pReady L c b) ((X.tr g).take k) + 0) % 2 := by
  have hg : g < L.threads := event_thread_lt hX he
  have hk : k < (X.tr g).length := len_of_get he
  rcases (poll_class hpre hX hf he).2.2 with
    ⟨d, -, -, hm, -⟩ | ⟨d, -, -, hm, -⟩ | ⟨d, P', -, -, hm⟩ | ⟨d, P', -, -, hm⟩ |
    ⟨d, P, hσ, hs, hm, hp⟩ | ⟨d, -, -, hm, -⟩
  rotate_left 4
  all_goals try hs_loc hm
  have hm' := hm
  simp only [EvW.pReady, barLoc_eq, EvW.pReadyOff] at hm'
  obtain ⟨hc, hbi⟩ := hm'
  subst hc
  have hb' : (d.i - 1) % 2 = b := by omega
  have hcnt := (mma_cnt hpre hX hf hR hg hk hσ).1 b hb
  rw [hcnt, hp]
  simp only [SO.Mm.pPolled, hs, below2]
  omega

/-- **The parity of a successful poll of `o_done`.** -/
theorem o_parity (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c g k pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (oDone L c) p true acq sc⟩) :
    p % 2 = (okPolls (oDone L c) ((X.tr g).take k) + 0) % 2 := by
  have hg : g < L.threads := event_thread_lt hX he
  have hk : k < (X.tr g).length := len_of_get he
  rcases (poll_class hpre hX hf he).2.2 with
    ⟨d, -, -, hm, -⟩ | ⟨d, hσ, hs, hm, hp⟩ | ⟨d, P', -, -, hm⟩ | ⟨d, P', -, -, hm⟩ |
    ⟨d, P', -, -, hm, -⟩ | ⟨d, -, -, hm, -⟩
  rotate_left 2
  all_goals try hs_loc hm
  have hm' := hm
  simp only [EvW.oDone, barLoc_eq, EvW.oDoneOff] at hm'
  obtain ⟨hc, -⟩ := hm'
  subst hc
  have hcnt := (Rd.sm_cnt hpre hX hf hg k hk.le _ hσ).2 d rfl
  have h1 : 1 ≤ d.i := hcnt.ok hs
  rw [hcnt.o, hp]
  simp only [SO.smOPolled, hs, SO.oDoneParity]
  omega

/-! ### `o_final` -/

/-- The successful polls of `o_final` a default-partition state has made. -/
def fCnt : DComp.St → Nat
  | .epi d => SO.epiPolled d
  | _ => 0

/-- **The states an epilogue state comes from**: the softmax region's exit (the epilogue's entry
state, at `wait`) or the epilogue itself. -/
theorem dnext_epi {s0 : DComp.St} {d : Epi.D} {e : Event}
    (h : DComp.next L g Q s0 e = some (some (DComp.St.epi d))) :
    (∃ d0, s0 = .sm d0 ∧ d.site = .wait) ∨ ∃ de, s0 = .epi de ∧ Epi.next de e = some (some d) := by
  cases s0 with
  | dstart dd =>
    change DComp.dstartNext L g Q dd e = _ at h
    unfold DComp.dstartNext at h
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
    split at ha <;> cases ha
  | pro dp =>
    change DComp.proNext L g Q dp e = _ at h
    unfold DComp.proNext at h
    split at h
    · split at h <;> cases h
    · obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
      cases ha
  | sm d0 =>
    change DComp.smNext L g d0 e = _ at h
    unfold DComp.smNext at h
    split at h
    · unfold DComp.exitNext at h
      split at h
      · simp only [Option.some.injEq, DComp.St.epi.injEq] at h
        refine .inl ⟨d0, rfl, ?_⟩
        rw [← h]
        split <;> rfl
      · cases h
    · obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
      cases ha
  | epi de =>
    change (Epi.next de e).map (Option.map DComp.St.epi) = _ at h
    obtain ⟨a, ha, hs⟩ := map_map_eq_some_some h
    simp only [DComp.St.epi.injEq] at hs
    subst hs
    exact .inr ⟨de, rfl, ha⟩

/-- An event at a default-partition state other than the epilogue's is no successful poll of
`o_final`. -/
theorem okPoll_f_notEpi (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {e : Event} {s : DComp.St}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d s)))
    (hs : ∀ d, s ≠ .epi d) : okPoll (oFinal L (g / L.block)) e = false := by
  cases hok : okPoll (oFinal L (g / L.block)) e with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨p, acq, sc, hev⟩ := okPoll_true hok
    rw [hev] at he
    rcases (poll_class hpre hX hf he).2.2 with
      ⟨d, -, -, hm, -⟩ | ⟨d, -, -, hm, -⟩ | ⟨d, P', h', -, -⟩ | ⟨d, P', h', -, -⟩ |
      ⟨d, P', h', -, -, -⟩ | ⟨d, h', -, -, -⟩
    · hs_loc hm
    · hs_loc hm
    all_goals rw [hσ] at h'
    all_goals simp only [Option.some.injEq, reduceCtorEq, TSt.d.injEq] at h'
    exact hs d h'

/-- **The successful polls of `o_final` along a default-partition thread's states.** -/
theorem epi_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) :
    ∀ (k : Nat), k ≤ (X.tr g).length → ∀ s : DComp.St,
      St Q L X g k = some (some (.d s)) →
        okPolls (oFinal L (g / L.block)) ((X.tr g).take k) = fCnt s := by
  have hS := ProA.sharedOk_of_pre hpre
  intro k
  induction k with
  | zero =>
    intro _ s hσ
    rcases pred_d (Nat.zero_le _) hσ with ⟨-, rfl⟩ | ⟨k0, -, -, h, -⟩
    · simp [okPolls, fCnt]
    · omega
  | succ k0 ih =>
    intro hk s hσ
    rcases pred_d hk hσ with ⟨h, -⟩ | ⟨k1, e, s0, hk1, he, hσ0, hn⟩
    · omega
    · have hk10 : k1 = k0 := by omega
      subst hk10
      have hge : X.get (g, k1) = some e := he
      have h0 := ih (by omega) s0 hσ0
      rw [Rd.okPolls_take_succ _ he, h0]
      cases s with
      | epi d =>
        rcases dnext_epi hn with ⟨d0, rfl, hw⟩ | ⟨de, rfl, hn'⟩
        · rw [okPoll_f_notEpi hpre hX hf hge hσ0 (by intro d h; cases h)]
          simp [fCnt, SO.epiPolled, hw]
        · have hnx : ¬ ExitState (.d (.epi de)) := by
            intro hx
            simp only [ExitState] at hx
            simp [Epi.next, hx] at hn'
          obtain ⟨u, hF⟩ := fired_cont hX hf hg hge hσ0 hnx
          obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hge hσ0
          have hi : Epi.Inv de := hinv.2.1
          have hm : Epi.Means Q L g de.pr := (treach_stateAt hpre hg hσ0).2
          rw [SO.epi_okPoll_f hS hm (fired_epi hF)]
          simp only [fCnt, SO.epi_next_polled hi hn']
          by_cases hw : de.site = .wait <;> by_cases ho : Ring.okW e = true <;> simp [hw, ho]
      | _ =>
        have hne : ∀ d, s0 ≠ .epi d := by
          intro d h
          subst h
          change (Epi.next d e).map (Option.map DComp.St.epi) = _ at hn
          obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
          cases ha
        rw [okPoll_f_notEpi hpre hX hf hge hσ0 hne]
        cases s0 with
        | epi d => exact absurd rfl (hne d)
        | _ => simp [fCnt]

/-- **The parity of a successful poll of `o_final`**: it is the thread's first. -/
theorem f_parity (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c g k pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (oFinal L c) p true acq sc⟩) :
    p % 2 = (okPolls (oFinal L c) ((X.tr g).take k) + 0) % 2 := by
  have hg : g < L.threads := event_thread_lt hX he
  have hk : k < (X.tr g).length := len_of_get he
  rcases (poll_class hpre hX hf he).2.2 with
    ⟨d, -, -, hm, -⟩ | ⟨d, -, -, hm, -⟩ | ⟨d, P', -, -, hm⟩ | ⟨d, P', -, -, hm⟩ |
    ⟨d, P', -, -, hm, -⟩ | ⟨d, hσ, hs, hm, hp⟩
  rotate_left 5
  all_goals try hs_loc hm
  have hm' := hm
  simp only [EvW.oFinal, barLoc_eq, EvW.oFinalOff] at hm'
  obtain ⟨hc, -⟩ := hm'
  subst hc
  rw [epi_cnt hpre hX hf hg k hk.le _ hσ, hp]
  simp [fCnt, SO.epiPolled, hs]

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
