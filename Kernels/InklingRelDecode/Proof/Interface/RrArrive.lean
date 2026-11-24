-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg
public import Kernels.InklingRelDecode.Proof.Interface.SyncFacts
public import Kernels.InklingRelDecode.Proof.Protocol.RdSmCount
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmRun
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneLoop

@[expose] public section

/-!
# Thread 0 of the default partition arrives on `p_ready` once per iteration

In a complete execution thread 0 of a CTA passes the site `arrive` of every iteration
`i < num_iters`, with the arrival `arrive (p_ready (i % 2)) 0 1 release cta`, and its earlier
arrivals on `p_ready (i % 2)` number `i / 2`.

* `succ_sm`: one step of the softmax region on the thread's states;
* `sm_reaches_arrive`: the backward induction of `Interface.sm_reaches_tmemSt` up to `bar21`, one
  step on to `arrive` (thread 0's `bar21` is followed by the arrival: `Sm.next`);
* `arr_cnt`: along the thread's states the arrivals on `p_ready b` number `below2 b d.i` at a
  softmax state `d` (and none before the region: the prologue's arrivals are on `kv_ready`), the
  analogue of `Rd.sm_cnt` for the arrivals.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rr
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.SO
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **Thread 0 of the CTA of thread `g`**: a launched thread of the default partition of the same
CTA, whose request and split are `g`'s. -/
theorem thread0 (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) :
    ∃ g0, g0 < L.threads ∧ g0 / L.block = g / L.block ∧ g0 % L.block = 0 ∧
      ProA.cta L g0 .z = ProA.cta L g .z ∧ ProA.cta L g0 .x = ProA.cta L g .x := by
  have hb : L.block = 256 := hpre.block
  have hpos : 0 < L.block := by omega
  have h1 : g / L.block * L.block ≤ g := Nat.div_mul_le_self _ _
  have h2 : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hpos
  refine ⟨g / L.block * L.block, by omega, h2, Nat.mul_mod_left _ _, ?_, ?_⟩
  · unfold ProA.cta
    rw [h2]
  · unfold ProA.cta
    rw [h2]

/-- **One step of the softmax region on the thread's states.** -/
theorem succ_sm {k : Nat} {d d' : Sm.D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hl : ¬ DComp.leaves L g d e)
    (hn : Sm.next L g d e = some (some d')) :
    St Q L X g (k + 1) = some (some (.d (.sm d'))) := by
  have he' : (X.tr g)[k]? = some e := he
  have hst : St Q L X g (k + 1) = (threadCode L g Q).next (.d (.sm d)) e := by
    have : Frame.stateAt (code L Q) X g k = some (some (.d (.sm d))) := hσ
    show Frame.stateAt (code L Q) X g (k + 1) = _
    rw [Frame.stateAt_succ he', this]
    rfl
  have hsm : DComp.next L g Q (.sm d) e = (Sm.next L g d e).map (Option.map DComp.St.sm) := by
    show DComp.smNext L g d e = _
    unfold DComp.smNext
    simp only [hl, ↓reduceIte]
  rw [hst, next_d, hsm, hn]
  rfl

/-- **A softmax state at an event has the thread's `num_iters` as its bound** (`Sm.Ent.r26`). -/
theorem r26_eq (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {d : Sm.D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    d.e.r26 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
  have hI := Sv.sm_inv_at hX hf he hσ
  have hm := ((hf.reach hg hσ).2 : SmMeans Q L g d.e)
  have hr25 := hm.ent.r25
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hn31 := numIters_lt31 hpre hz (ProA.cta L g .x)
  have h1 := hI.ok.r26
  rw [hr25] at h1
  rw [h1]
  simp only [hn31, ↓reduceIte]

/-- **A launched thread whose last event is an exit exits from an exit state.** -/
theorem exit_of_last (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    ∃ k pc, X.get (g, k) = some ⟨pc, .exit⟩ ∧
      ((∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .exit) ∨
      (∃ x : WComp.ExitD, St Q L X g k = some (some (.w (.exit x))) ∧ x.site = .ret)) := by
  obtain ⟨pc, hl⟩ := hex
  have hlen : 0 < (X.tr g).length := by
    by_contra h0
    have : (X.tr g) = [] := List.length_eq_zero_iff.mp (by omega)
    rw [this] at hl
    simp at hl
  have hge : (X.tr g)[(X.tr g).length - 1]? = some ⟨pc, .exit⟩ := by
    rw [← List.getLast?_eq_getElem?, hl]
  exact ⟨(X.tr g).length - 1, pc, hge, exit_event_state hX hf.sound hf.tracked hge⟩

/-- **A state of a thread whose last event is an exit is at an event.** -/
theorem lt_length_of_last (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) {k : Nat}
    {s : TSt} (h : St Q L X g k = some (some s)) : k < (X.tr g).length := by
  by_contra hk
  have h2 : St Q L X g (X.tr g).length = some (some s) :=
    (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k) (by omega)).symm.trans h
  obtain ⟨pc, hl⟩ := hex
  have hlen : 0 < (X.tr g).length := by
    by_contra h0
    have : (X.tr g) = [] := List.length_eq_zero_iff.mp (by omega)
    rw [this] at hl
    simp at hl
  have he : (X.tr g)[(X.tr g).length - 1]? = some ⟨pc, .exit⟩ := by
    rw [← List.getLast?_eq_getElem?, hl]
  have hge : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := he
  have hlen' : (X.tr g).length = ((X.tr g).length - 1) + 1 := by omega
  rw [hlen', St, Frame.stateAt_succ he] at h2
  rcases exit_event_state hX hf.sound hf.tracked hge with ⟨d, hσ, hd⟩ | ⟨x, hσ, hx⟩
  · have hσ' : Frame.stateAt (code L Q) X g ((X.tr g).length - 1) =
        some (some (.d (.epi d))) := hσ
    rw [hσ'] at h2
    simp only [Option.bind_some] at h2
    have := next_epiExit_none (L := L) (Q := Q) (g := g) d hd ⟨pc, .exit⟩
    simp only [Code.toMachine] at h2
    exact absurd (this.symm.trans h2) (by simp)
  · have hσ' : Frame.stateAt (code L Q) X g ((X.tr g).length - 1) =
        some (some (.w (.exit x))) := hσ
    rw [hσ'] at h2
    simp only [Option.bind_some] at h2
    obtain ⟨xs, P⟩ := x
    have hx' : xs = .ret := hx
    subst hx'
    have := next_ret_none (L := L) (Q := Q) (g := g) P ⟨pc, .exit⟩
    simp only [Code.toMachine] at h2
    exact absurd (this.symm.trans h2) (by simp)

/-- A thread of a complete execution has an exit as its last event. -/
theorem last_of_complete (hX : Consistent L kernel asms mem0 X) (hc : Complete L X)
    (hg : g < L.threads) : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩ := by
  rcases hc.1 g hg with hcan | h
  · exact absurd hcan (no_canceled hX g hg)
  · exact h

/-- **Every softmax thread reaches `bar21` of every iteration.** -/
theorem sm_reaches_bar21 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (hdef : g % L.block < 128) {i0 : Nat}
    (hi : i0 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) :
    ∃ (k : Nat) (ds : Sm.D), St Q L X g k = some (some (.d (.sm ds))) ∧ ds.site = .bar21 ∧
      ds.i = i0 ∧ k < (X.tr g).length := by
  obtain ⟨kx, pcx, hgetx, hx⟩ := exit_of_last hX hf hex
  have hkx : kx < (X.tr g).length := len_of_get hgetx
  obtain ⟨d, hσx, -⟩ : ∃ d : Epi.D, St Q L X g kx = some (some (.d (.epi d))) ∧
      d.site = .exit := by
    rcases hx with h | ⟨x, hσ, -⟩
    · exact h
    · exfalso
      obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hgetx hσ
      have : ¬ IsDefault L g := hinv.1
      exact this hdef
  obtain ⟨k0, e0, d0, hk0, he0, hσ0, hl⟩ := epi_back kx hkx.le hσx
  have hge0 : X.get (g, k0) = some e0 := he0
  have hI := Sv.sm_inv_at hX hf hge0 hσ0
  have hr26 : d0.e.r26 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) :=
    r26_eq hpre hX hf hg hge0 hσ0
  have hleave := Sv.leaveSite_of_leaves hl
  have hlast : d0.i + 1 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) ∧
      (d0.site = .bar21 ∨ d0.site = .arrive) := by
    rcases hleave with ⟨hs, he⟩ | ⟨j, hs, he⟩ | ⟨hs, he⟩
    · exfalso
      have := (hI.loop.2 hs).1
      omega
    · exfalso
      have := (hI.loop.1 j hs).1
      omega
    · exact ⟨by omega, hs⟩
  obtain ⟨k', d', hk', hσ', hs', hi'⟩ := bar21_back i0 k0 (by omega) hσ0
    (by rcases Nat.lt_or_ge i0 d0.i with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, hlast.2⟩)
  exact ⟨k', d', hσ', hs', hi', by omega⟩

/-- **Thread 0 of a CTA arrives on `p_ready (i % 2)` in every iteration `i < num_iters`.** -/
theorem sm_reaches_arrive (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (hlead : g % L.block = 0) {i0 : Nat}
    (hi : i0 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) :
    ∃ (k pc : Nat) (ds : Sm.D), St Q L X g k = some (some (.d (.sm ds))) ∧ ds.site = .arrive ∧
      ds.i = i0 ∧
      X.get (g, k) = some ⟨pc, .arrive (pReady L (g / L.block) (i0 % 2)) 0 1 true .cta⟩ := by
  obtain ⟨k', d', hσ', hs', hi', hk'⟩ :=
    sm_reaches_bar21 hpre hX hf hg hex (by omega) hi
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, k') = some e' := ⟨_, List.getElem?_eq_getElem hk'⟩
  have hl : ¬ DComp.leaves L g d' e' := by
    unfold DComp.leaves
    rw [hs']
    simp [hlead]
  have hn : Sm.next L g d' e' = some (some { d' with site := .arrive }) := by
    simp [Sm.next, hs', hlead]
  have hσ2 := succ_sm he' hσ' hl hn
  generalize hd2 : ({ d' with site := .arrive } : Sm.D) = d2 at hσ2
  have hs2 : d2.site = .arrive := by rw [← hd2]
  have hi2 : d2.i = i0 := by rw [← hd2]; exact hi'
  have hk2 := lt_length_of_last hX hf hex hσ2
  obtain ⟨e2, he2⟩ : ∃ e2, X.get (g, k' + 1) = some e2 :=
    ⟨_, List.getElem?_eq_getElem hk2⟩
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he2 hσ2 (by simp [ExitState])
  obtain ⟨-, hev⟩ := Sm.shape_arrive (Sm.sharedOk_of_pre hpre) (fired_sm hF) hs2
  refine ⟨k' + 1, Sm.evPc d2.site, d2, hσ2, hs2, hi2, ?_⟩
  rw [he2, hev, loc_pReadyOf, hi2]

theorem arrivals_take_succ (m : Loc) {l : List Event} {k : Nat} {e : Event}
    (he : l[k]? = some e) :
    arrivals m (l.take (k + 1)) =
      arrivals m (l.take k) + (if arrivesOn m e = true then 1 else 0) := by
  unfold arrivals
  rw [List.take_add_one, he]
  simp [List.countP_append]

/-- **The arrivals on `p_ready` along the thread's states.** For a thread of the CTA's thread 0
(`g % block = 0`), at every softmax state the arrivals on `p_ready b` number `below2 b d.i`, and
before the region there are none (the prologue's arrivals are on `kv_ready`). -/
theorem arr_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) (hlead : g % L.block = 0) :
    ∀ (k : Nat), k ≤ (X.tr g).length → ∀ s : DComp.St,
      St Q L X g k = some (some (.d s)) →
      (PreSt s → ∀ b < 2, arrivals (pReady L (g / L.block) b) ((X.tr g).take k) = 0) ∧
      ∀ d, s = .sm d → ∀ b < 2,
        arrivals (pReady L (g / L.block) b) ((X.tr g).take k) = below2 b d.i := by
  have hS := Sm.sharedOk_of_pre hpre
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk s hσ
    rcases pred_d hk hσ with ⟨rfl, rfl⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
    · refine ⟨fun _ b _ => by simp [arrivals], ?_⟩
      intro d hd
      cases hd
    · have hk0 : k0 ≤ (X.tr g).length := by omega
      have hge : X.get (g, k0) = some e := he
      obtain ⟨hp0, hs0⟩ := ih k0 (by omega) hk0 s0 hσ0
      have hpreE : ∀ b, b < 2 → PreSt s0 →
          arrivesOn (pReady L (g / L.block) b) e = false := by
        intro b hb hp0'
        by_cases hk' : ∃ l tx c rel sc, e.kind = .arrive l tx c rel sc
        · rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg hge hk' with
            ⟨d, -, j, hj, -, hev⟩ | ⟨d, hσd, -⟩ | ⟨d, P, hσd, -⟩
          · rw [hev]
            have hne := SO.kvReady_ne_pReady (L := L) (c := g / L.block) (s := j) hj hb
            have : (EvD.kvReadyOf j).loc L (g / L.block) = EvW.kvReady L (g / L.block) j := by
              simp only [EvD.kvReadyOf, EvD.Bar.loc, EvD.Bar.off, EvW.kvReady, EvW.barLoc,
                EvW.kvReadyOff, Nat.mod_eq_of_lt hj]
            simp [arrivesOn, sourceArrive, this, hne]
          · rw [hσ0] at hσd
            simp only [Option.some.injEq, TSt.d.injEq] at hσd
            subst hσd
            exact absurd hp0' (by simp [PreSt])
          · rw [hσ0] at hσd
            cases hσd
        · exact arrivesOn_false (fun l tx c rel sc h => hk' ⟨l, tx, c, rel, sc, h⟩)
      refine ⟨fun hpr => ?_, fun d hd => ?_⟩
      · have hpre0 := dnext_pre hn hpr
        have hp := hp0 hpre0
        intro b hb
        rw [arrivals_take_succ _ he, hp b hb, hpreE b hb hpre0]
        rfl
      · subst hd
        rcases dnext_sm hn with ⟨dp, rfl, rfl⟩ | ⟨d0, rfl, hn0⟩
        · intro b hb
          rw [arrivals_take_succ _ he, hp0 trivial b hb, hpreE b hb trivial]
          simp [SmEntry.d0, below2_zero]
        · intro b hb
          obtain ⟨u, hF⟩ := fired_cont hX hf hg hge hσ0 (by simp [ExitState])
          have hF' := fired_sm hF
          have hi := sm_next_arrived hlead hn0
          rw [arrivals_take_succ _ he, hs0 d0 rfl b hb, SO.sm_arrivesOn_p hS hF', hi]
          by_cases hs : d0.site = .arrive
          · by_cases hm : d0.i % 2 = b
            · simp [hs, hm, below2_succ hb]
            · simp [hs, hm, below2_succ hb]
          · simp [hs]

end
end PTX.Kernels.InklingRelDecode.Proof.Rr
