-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.WkLdEnd
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-!
# The loader's arrivals, copies and elections at a state up to the end of its trace

As `Wk.ld_polls_le` for the polls: the anchored run of a loader state (`Lp.loader_anchor`) extends
by one step to a state after the last event (`Wk.ld_pred_le`). Along it

* lane 0's arrivals on `kv_ready s` are `below s (arrIters d) - below s num_pre`
  (`ld_arr_le`, `Ring.loader_arrives`);
* a lane that led every election of its trace has issued `cpMu s d - 8 · below s num_pre` copies
  completing on `kv_ready s` (`ld_cp_le`, `Ring.loader_copies`);
* every lane has made at least `4 (i - num_pre) + elOff site` elections (`el_le`, by induction over
  the states: the loader's four elections per iteration at `el0` … `el3`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lp (PreSite)
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)
open PTX.Kernels.InklingRelDecode.Proof.Wk (np)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
include hpre hX hf hR hp

/-- The anchored run of a loader state after the anchor, at an index up to the trace's length. -/
theorem ld_window_le {k : Nat} {d : Loader.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hnp : ¬ PreSite d.site)
    (hb : d.site ≠ .bar0) :
    g < L.threads ∧ 4 ≤ WComp.warpOf L g ∧ ∃ (k0 : Nat) (d0 : Loader.D), k0 ≤ k ∧
      wAt Q L X g k0 = some (some (.loader d0 P)) ∧ d0.site = .bar0 ∧ d0.i = np Q L g ∧
      (∀ m, arrivals m ((X.tr g).take k0) = 0) ∧
      (∀ m, ((X.tr g).take k0).countP (issuesTo m) = 0) ∧
      (WComp.code L g Q).toMachine.Trace (some (.loader d0 P))
        (((X.tr g).drop k0).take (k - k0)) ∧
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        (((X.tr g).drop k0).take (k - k0)) = some (some (.loader d P)) ∧
      ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
        (WComp.code L g Q).toMachine.after (some (.loader d0 P))
          ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
        Ring.Ld.InLoop d' ∧ d'.site ≠ .setMaxInc ∧ Loader.Inv L g d' := by
  obtain ⟨k1, e, d1, hadj, hg, he, hσ1, hn⟩ := Wk.ld_pred_le hX hk hσ (fun h => hnp (.inl h))
  have hk1 : k1 < (X.tr g).length := by omega
  obtain ⟨-, -, -, h4, h5, h6⟩ := Lp.next_pre hn
  have hp1 : ¬ PreSite d1.site := by
    rintro (h | h | h)
    · exact hnp (.inr (.inl (h4 h)))
    · exact hnp (.inr (.inr (h5 h)))
    · exact hb (h6 h)
  obtain ⟨hw, k0, d0, hk0, h0, hd1, hs0, hi0, hin, hA, -, hI⟩ :=
    Lp.loader_anchor hpre hX hf hR hp hk1 hσ1 hp1
  have hd : wAt Q L X g k = some (some (.loader d P)) := Rd.wAt_of_st _ hk hσ
  have hin2 : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.loader d' P)) ∧
      Ring.Ld.InLoop d' ∧ d'.site ≠ .setMaxInc := by
    intro j hj1 hj2
    by_cases hj : j = k1
    · subst hj
      exact ⟨d1, hd1, ⟨fun h => hp1 (.inl h), fun h => hp1 (.inr (.inl h)),
        fun h => hp1 (.inr (.inr h)), hf.ldRng hg hσ1⟩, (Lp.next_ne_setMaxDec hn).2⟩
    · exact hin j hj1 (by omega)
  have hkk : k0 ≤ k := by omega
  have hrun := Ring.run_from hpre hw hg hX k h0
  obtain ⟨hend, hmid⟩ := Ring.run_states hkk h0 hd
  refine ⟨hg, hw, k0, d0, hkk, h0, hs0, hi0, hA, hI, hrun, hend, fun j hj => ?_⟩
  have hj' : j < k - k0 := lt_of_lt_of_le hj (List.length_take_le _ _)
  obtain ⟨d', h1, h2, h3⟩ := hin2 (k0 + j) (by omega) (by omega)
  exact ⟨d', (hmid j hj').trans h1, h2, h3,
    Ring.loader_inv_at hpre hw hg hX (j := k0 + j) (by omega) h1⟩

omit hpre hX hf hR hp in
/-- The anchor of a state after it is before it. -/
theorem anchor_lt {k k0 : Nat} {d d0 : Loader.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hb : d.site ≠ .bar0)
    (h0 : wAt Q L X g k0 = some (some (.loader d0 P))) (hs0 : d0.site = .bar0) (hkk : k0 ≤ k) :
    k0 < (X.tr g).length := by
  by_contra hc
  have hk0 : k0 = k := by omega
  subst hk0
  have := Rd.wAt_of_st _ hk hσ
  rw [h0] at this
  simp only [Option.some.injEq, WComp.WSt.loader.injEq] at this
  exact hb (this.1 ▸ hs0)

/-- **Lane 0's arrivals at a state up to the trace's end.** -/
theorem ld_arr_le {k : Nat} {d : Loader.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hI : Loader.Inv L g d)
    (hnp : ¬ PreSite d.site) (hb : d.site ≠ .bar0) (hne : ∀ e ∈ X.tr g, ¬ Ends e)
    (hl : laneOf L g = 0) :
    ∀ s < 3, arrivals (kvReady L (g / L.block) s) ((X.tr g).take k) +
      Ring.below s (np Q L g) = Ring.below s (Ring.Ld.arrIters d) := by
  intro s hs
  obtain ⟨hg, hw, k0, d0, hkk, h0, hs0, hi0, hA, -, hrun, hend, hwin⟩ :=
    ld_window_le hpre hX hf hR hp hk hσ hnp hb
  have hmap : EvW.MapReg P := EvW.after_mapReg (Rd.wAt_of_st _ hk hσ)
  have hnE : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), ¬ Ends e := fun e he =>
    hne e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  have hin' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
      Ring.Ld.InLoop d' ∧ d'.site ≠ .setMaxInc ∧ (d'.site = .arrive → d'.ln = true) := by
    intro j hj
    obtain ⟨d', h1, h2, h3, h4⟩ := hwin j hj
    exact ⟨d', h1, h2, h3, h4.lane⟩
  have h := Ring.loader_arrives hpre hmap hrun hnE hin' hend s hs
  have hI0 := Ring.loader_inv_at hpre hw hg hX (anchor_lt hk hσ hb h0 hs0 hkk) h0
  have hln0 : d0.ln = true := by rw [hI0.ln]; simp [hl]
  have hlnd : d.ln = true := by rw [hI.ln]; simp [hl]
  have hai0 : Ring.Ld.arrIters d0 = d0.i := by
    simp [Ring.Ld.arrIters, Ring.Ld.afterArrive, hs0]
  simp only [Ring.Ld.arrMu, hln0, hlnd, ite_true, hai0, hi0] at h
  unfold arrivals
  rw [Ring.countP_take_split _ _ hkk]
  have := hA (kvReady L (g / L.block) s)
  unfold arrivals at this
  rw [this, Nat.zero_add]
  exact h

/-- **A leading lane's copies at a state up to the trace's end.** -/
theorem ld_cp_le {k : Nat} {d : Loader.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hnp : ¬ PreSite d.site)
    (hb : d.site ≠ .bar0) (hne : ∀ e ∈ X.tr g, ¬ Ends e) (hlead : ElectLead L g (X.tr g)) :
    ∀ s < 3, ((X.tr g).take k).countP (issuesTo (kvReady L (g / L.block) s)) +
      8 * Ring.below s (np Q L g) = Ring.Ld.cpMu s d := by
  intro s hs
  obtain ⟨hg, hw, k0, d0, hkk, h0, hs0, hi0, -, hC, hrun, hend, hwin⟩ :=
    ld_window_le hpre hX hf hR hp hk hσ hnp hb
  have hmap : EvW.MapReg P := EvW.after_mapReg (Rd.wAt_of_st _ hk hσ)
  have hE : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), Ring.LeadRun L g e := fun e he =>
    have hm := List.mem_of_mem_drop (List.mem_of_mem_take he)
    ⟨hne e hm, hlead e hm⟩
  have hin' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
      Ring.Ld.InLoop d' ∧ d'.site ≠ .setMaxInc := by
    intro j hj
    obtain ⟨d', h1, h2, h3, -⟩ := hwin j hj
    exact ⟨d', h1, h2, h3⟩
  have h := Ring.loader_copies hpre hmap hrun hE hin' hend s hs
  have hc0 : Ring.Ld.cpMu s d0 = 8 * Ring.below s d0.i := by
    simp [Ring.Ld.cpMu, Ring.Ld.cpIn, hs0]
  rw [hc0, hi0] at h
  rw [Ring.countP_take_split _ _ hkk, hC, Nat.zero_add]
  exact h

end

/-! ### The elections of a loader lane -/

/-- The elections of a loader iteration before the site. -/
def elOff : Loader.Site → Nat
  | .cp0a | .cp0b | .wb2 | .el1 => 1
  | .cp1a | .cp1b | .ldb1 | .wb3 | .el2 => 2
  | .cp2a | .cp2b | .wb4 | .el3 => 3
  | .cp3a | .cp3b => 4
  | _ => 0

/-- The election sites of the loader. -/
def elB : Loader.Site → Nat
  | .el0 | .el1 | .el2 | .el3 => 1
  | _ => 0

/-- The elections of thread `g` before its event `k`. -/
def elects (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP isElectEv

/-- **One step of the loader in the loop** adds the election bit of the site. -/
theorem el_next {d0 d : Loader.D} {e : Event} (hn : Loader.next L g d0 e = some (some d))
    (hp : ¬ PreSite d0.site) :
    4 * d.i + elOff d.site = 4 * d0.i + elOff d0.site + elB d0.site := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d0
  simp only [PreSite, not_or] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  cases s <;> simp only [Loader.next, Loader.afterIter] at hn <;> (repeat' split at hn) <;>
    first
    | (simp at h1; done) | (simp at h2; done) | (simp at h3; done)
    | (simp at hn; done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn)
       simp_all [elOff, elB]; done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn)
       simp_all [elOff, elB]; omega)

/-- The event of a loader state is an election exactly at an election site. -/
theorem el_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {e : Event} {d : Loader.D} {P : Loader.Pro}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.w (.loader d P)))) :
    (if isElectEv e then 1 else 0) = elB d.site := by
  have hsh := Lp.loader_ev_shape hpre hX hf he hσ
  unfold EvW.LdShape at hsh
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only at hsh <;>
    first
    | (obtain ⟨_, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl, -⟩ := hsh; rfl)

/-- **The elections before a loader state of the loop** are at least
`4 (i - num_pre) + elOff site`. -/
theorem el_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hp : NumPreRead Q L X) :
    ∀ k, k ≤ (X.tr g).length → ∀ {d : Loader.D} {P : Loader.Pro},
      St Q L X g k = some (some (.w (.loader d P))) → ¬ PreSite d.site →
      4 * d.i + elOff d.site ≤ elects X g k + 4 * np Q L g := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d P hσ hnp
    by_cases hb : d.site = .bar0
    · have hi : d.i = np Q L g := Interface.Lk.ipre_inv hpre hX hf hp k _ hσ (.inr hb)
      rw [hi, hb]
      simp [elOff]
    · obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ :=
        Wk.ld_pred_le hX hk hσ (fun h => hnp (.inl h))
      obtain ⟨-, -, -, h4, h5, h6⟩ := Lp.next_pre hn
      have hp0 : ¬ PreSite d0.site := by
        rintro (h | h | h)
        · exact hnp (.inr (.inl (h4 h)))
        · exact hnp (.inr (.inr (h5 h)))
        · exact hb (h6 h)
      have ih0 := ih k0 (by omega) (by omega) hσ0 hp0
      have hstep := el_next hn hp0
      have hev := el_event hpre hX hf he hσ0
      have hsucc : elects X g k = elects X g k0 + (if isElectEv e then 1 else 0) := by
        subst hadj
        unfold elects
        have he' : (X.tr g)[k0]? = some e := he
        rw [List.take_add_one, he', Option.toList_some, List.countP_append]
        simp
      rw [hsucc, hev]
      omega

end
end PTX.Kernels.InklingRelDecode.Proof.Wm
