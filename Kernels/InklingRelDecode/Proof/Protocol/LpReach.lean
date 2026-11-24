-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpRun
public import Lemmas.Flow.ElectLead

@[expose] public section

/-!
# The loader warp reaches every copy of every block it loads

Progress backward from the exit of a thread of warp 6, the analogue of `Rr.sm_reaches_bar21` for
the loader:

* `exists_wrap`: a worker thread that exited has left a role through the role's last site: the
  register-request count `rqN` is `(tPh s).1 + 3 t` with `t` the rounds of the dispatch loop
  (`phase_inv`), `t` grows only at a role's last site (`w_next`), and the exit is after one round;
  for warp 6 that site is the loader's `setMaxInc` (`roleWarp_inv`);
* `rank`: a number of each loader state, `20 i + pos site`, which a step of a thread that led its
  elections (`ElectLead`) raises by at most one (`rank_step`): the elected lane passes every copy
  site;
* `reach_rank`: backward from a state of rank at least `R`, a state of rank exactly `R` (the anchor
  `bar0` has rank `20 num_pre`, below `R`);
* `loader_reaches`: a thread of warp 6 that exited and led its elections has a state at every site
  after `ldb0` of every iteration `num_pre ≤ i < num_iters`;
* `exists_lead`: warp 6 of a CTA has a thread that led its elections (the elections of a warp with
  one mask return one leader, `ElectOk`), which exited if every thread of the warp exited.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### A worker that exited left a role -/

/-- Without a role's last site among the earlier states, the request count of a worker state is
its phase's. -/
theorem rq_of_noWrap (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) :
    ∀ k, k ≤ (X.tr g).length → ∀ a, St Q L X g k = some (some (.w a)) →
      (∀ j < k, ∀ b, St Q L X g j = some (some (.w b)) → wrap b = 0) →
      rqN X g k = (wPh a).1 := by
  intro k
  induction k with
  | zero =>
    intro _ a hσ _
    obtain ⟨-, t, hr, -⟩ := phase_inv hpre hX hf.sound hR 0 _ (by omega) hσ
    have : rqN X g 0 = 0 := by simp [rqN]
    simp only [tPh] at hr
    omega
  | succ k ih =>
    intro hk a hσ hno
    have hs'' : Frame.stateAt (code L Q) X g (k + 1) = some (some (.w a)) := hσ
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ0 : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ0] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ0] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ0] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L g Q).next s e = some (some (.w a)) := hs''
        cases s with
        | d s0 =>
          rw [next_d] at hn
          obtain ⟨_, -, h⟩ := map_map_eq_some_some hn
          cases h
        | w b =>
          rw [next_w] at hn
          obtain ⟨a', ha, h⟩ := map_map_eq_some_some hn
          cases h
          have hσb : St Q L X g k = some (some (.w b)) := hσ0
          have hwb := hno k (by omega) b hσb
          have ih' := ih (by omega) b hσb (fun j hj b' hb' => hno j (by omega) b' hb')
          obtain ⟨hto, -⟩ := phase_inv hpre hX hf.sound hR k _ (by omega) hσb
          have hto' : wTo b = false := hto
          obtain ⟨h1, -⟩ := w_next ha hto'
          have hget : X.get (g, k) = some e := he
          obtain ⟨hreq, -⟩ := event_req hX hf.sound hget hσb
          have hrq : rqN X g (k + 1) = rqN X g k + rInc (wReqS b) := by
            unfold rqN
            rw [countP_take_succ _ he]
            by_cases hr : SetMaxNReg.isRequest e = true
            · have h2 : (tReq (.w b)).isSome = true := hreq.mp hr
              simp only [tReq] at h2
              simp [hr, h2, rInc_eq]
            · have h2 : ¬ (wReqS b).isSome = true := fun h => hr (hreq.mpr h)
              simp [hr, h2, rInc_eq]
          rw [hwb] at h1
          omega

/-- **A worker that exited left a role through its last site.** -/
theorem exists_wrap (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {kx : Nat} {x : WComp.ExitD}
    (hkx : kx < (X.tr g).length) (hσx : St Q L X g kx = some (some (.w (.exit x)))) :
    ∃ j b, j < kx ∧ St Q L X g j = some (some (.w b)) ∧ wrap b = 1 := by
  by_contra hno
  push Not at hno
  have hno' : ∀ j < kx, ∀ b, St Q L X g j = some (some (.w b)) → wrap b = 0 := by
    intro j hj b hb
    have h1 := wrap_le b
    have h2 := hno j b hj hb
    omega
  have hrq := rq_of_noWrap hpre hX hf hR kx hkx.le _ hσx hno'
  obtain ⟨-, t, hr, -, -, -, h2, -⟩ := phase_inv hpre hX hf.sound hR kx _ hkx.le hσx
  have ht : 1 ≤ t := h2 (by simp [tKind, wKind])
  simp only [tPh] at hr
  omega

/-- **A thread of warp 6 that exited has a loader state at `setMaxInc`.** -/
theorem exists_setMaxInc (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hw6 : g % L.block / 32 = 6)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    ∃ j d P, j < (X.tr g).length ∧ St Q L X g j = some (some (.w (.loader d P))) ∧
      d.site = .setMaxInc := by
  obtain ⟨kx, pcx, hgetx, hx⟩ := Rr.exit_of_last hX hf hex
  have hkx : kx < (X.tr g).length := len_of_get hgetx
  obtain ⟨x, hσx⟩ : ∃ x : WComp.ExitD, St Q L X g kx = some (some (.w (.exit x))) := by
    rcases hx with ⟨d, hσ, -⟩ | ⟨x, hσ, -⟩
    · exfalso
      obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hgetx hσ
      have : IsDefault L g := hinv.1
      unfold IsDefault at this
      omega
    · exact ⟨x, hσ⟩
  obtain ⟨j, b, hj, hσj, hwr⟩ := exists_wrap hpre hX hf hR hkx hσx
  have hrw := roleWarp_inv hf.roleWarp j _ (by omega) hσj
  cases b with
  | idle d =>
    simp only [RoleWarp, roleWarp] at hrw
    omega
  | mma d P =>
    simp only [RoleWarp, roleWarp] at hrw
    omega
  | loader d P =>
    refine ⟨j, d, P, by omega, hσj, ?_⟩
    simp only [wrap] at hwr
    split at hwr
    · assumption
    · cases hwr
  | worker w => simp [wrap] at hwr
  | exit x => simp [wrap] at hwr

/-! ### The loop's end -/

theorem next_into_setMaxInc {d0 d : Loader.D} {e : Event}
    (hn : Loader.next L g d0 e = some (some d)) (hs : d.site = .setMaxInc) :
    d0.site = .bar1 ∧ d.i = d0.i ∧ d.n = d0.n := by
  unfold Loader.next Loader.afterIter Loader.readI Loader.readN at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; (try split) <;> simp_all)

/-- The step into the exit barrier: from the loop's entry with `num_iters ≤ num_pre` (the counters
below `2 ^ 31`, `Loader.Rng`, so the signed compare is the compare of the numbers), or from the
iteration whose incremented counter register is `num_iters`. -/
theorem next_into_bar1 {d0 d : Loader.D} {e : Event} (hr : Loader.Rng d0)
    (hn : Loader.next L g d0 e = some (some d)) (hs : d.site = .bar1) : d.n ≤ d.i := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d0
  by_cases hb : site = .bar0
  · subst hb
    have hi := hr.bndI rfl
    have hn' := hr.bndN rfl
    simp only [Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      by_cases hc : Loader.sxI n ≤ Loader.sxI i
      · simp only [hc, ↓reduceIte]
        rw [Loader.sxI_of_lt hi, Loader.sxI_of_lt hn'] at hc
        simp only at hc
        exact (by omega : n ≤ i)
      · simp only [hc, ↓reduceIte] at hs
        cases hs
    · cases hn
  · unfold Loader.next Loader.afterIter Loader.readI Loader.readN at hn
    cases site <;> first
      | exact absurd rfl hb
      | ((repeat' split at hn)
         all_goals first
           | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
           | (simp only [Option.some.injEq] at hn; subst hn; (try split) <;> simp_all
              all_goals omega))

/-- At the role's last site the loop counter has reached `num_iters`. -/
theorem setMaxInc_ge (hX : Consistent L kernel asms mem0 X) (hrg : LdRng Q L X) {k : Nat}
    {d : Loader.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hs : d.site = .setMaxInc) :
    d.n ≤ d.i := by
  obtain ⟨k0, _, d0, hadj, -, -, hσ0, hn⟩ :=
    loader_state_pred_adj hX hk hσ (by rw [hs]; nofun)
  obtain ⟨hs0, hi, hnn⟩ := next_into_setMaxInc hn hs
  obtain ⟨k1, _, d1, -, -, -, hσ1, hn1⟩ :=
    loader_state_pred_adj hX (by omega) hσ0 (by rw [hs0]; nofun)
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (g, k) = some e0 := ⟨_, List.getElem?_eq_getElem hk⟩
  have := next_into_bar1 (hrg (Frame.lt_of_get hX he0) hσ1) hn1 hs0
  omega

/-! ### The rank of a loader state -/

/-- The place of a site in an iteration of the loop. -/
def pos : Loader.Site → Nat
  | .wait | .bar1 | .setMaxInc => 1
  | .wb0 | .arrive => 2
  | .ldb0 => 3 | .wb1 => 4 | .el0 => 5 | .cp0a => 6 | .cp0b => 7 | .wb2 => 8 | .el1 => 9
  | .cp1a => 10 | .cp1b => 11 | .ldb1 => 12 | .wb3 => 13 | .el2 => 14 | .cp2a => 15
  | .cp2b => 16 | .wb4 => 17 | .el3 => 18 | .cp3a => 19 | .cp3b => 20
  | .setMaxDec | .ld0 | .ld1 | .bar0 => 0

/-- The rank of a loader state: `20 i + pos site` in the loop, `0` before it. -/
def rank (d : Loader.D) : Nat :=
  match d.site with
  | .setMaxDec | .ld0 | .ld1 => 0
  | s => 20 * d.i + pos s

theorem rank_eq {d : Loader.D} (h : ¬ PreSite d.site) : rank d = 20 * d.i + pos d.site := by
  unfold rank
  unfold PreSite at h
  split <;> simp_all

theorem pos_le (s : Loader.Site) : pos s ≤ 20 := by cases s <;> simp [pos]

theorem pos_inj {a b : Loader.Site} (h : pos a = pos b) (h3 : 3 ≤ pos a) : a = b := by
  revert h h3
  cases a <;> cases b <;> decide

theorem pos_pos {s : Loader.Site} (h : ¬ PreSite s) (hb : s ≠ .bar0) : 1 ≤ pos s := by
  unfold PreSite at h
  cases s <;> simp_all [pos]

/-- **One step of a thread that leads its elections raises the rank by at most one.** -/
theorem rank_step {d0 d : Loader.D} {e : Event} (hn : Loader.next L g d0 e = some (some d))
    (hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
    (hp : ¬ PreSite d0.site) : rank d0 ≤ rank d ∧ rank d ≤ rank d0 + 1 := by
  unfold PreSite at hp
  unfold Loader.next Loader.afterIter Loader.readI Loader.readN at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; (try split) <;> simp_all [rank, pos]; done)
    | (simp only [Option.some.injEq] at hn; subst hn; (try split) <;> simp_all [rank, pos] <;>
        omega)

/-- **Backward to a state of a given rank.** For a thread that leads its elections, whose anchors
have rank below `R`: a loader state of rank at least `R` has, at an earlier or the same event, a
loader state of rank exactly `R`, in the loop and not the anchor. -/
theorem reach_rank (hX : Consistent L kernel asms mem0 X) (hlead : ElectLead L g (X.tr g))
    {R : Nat} (hR1 : 1 ≤ R)
    (hb : ∀ k d P, St Q L X g k = some (some (.w (.loader d P))) → d.site = .bar0 →
      20 * d.i < R) :
    ∀ k {d : Loader.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.loader d P))) → R ≤ rank d →
      ∃ k' d', k' ≤ k ∧ St Q L X g k' = some (some (.w (.loader d' P))) ∧ rank d' = R ∧
        ¬ PreSite d'.site ∧ d'.site ≠ .bar0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hr
    have hnp : ¬ PreSite d.site := by
      intro h
      have : rank d = 0 := by
        unfold rank; unfold PreSite at h
        rcases h with h | h | h <;> rw [h]
      omega
    by_cases hbar : d.site = .bar0
    · have h1 := hb k d P hσ hbar
      rw [rank_eq hnp, hbar] at hr
      simp [pos] at hr
      omega
    by_cases heq : rank d = R
    · exact ⟨k, d, le_refl _, hσ, heq, hnp, hbar⟩
    have hs0 : d.site ≠ .setMaxDec := fun h => hnp (.inl h)
    obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ := loader_state_pred_adj hX hk hσ hs0
    have hp0 : ¬ PreSite d0.site := by
      obtain ⟨-, -, -, h4, h5, h6⟩ := next_pre hn
      rintro (h | h | h)
      · exact hnp (.inr (.inl (h4 h)))
      · exact hnp (.inr (.inr (h5 h)))
      · exact hbar (h6 h)
    have hmem : e ∈ X.tr g := List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he)
    have hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g :=
      fun mask inst ld h => hlead e hmem mask inst ld h
    obtain ⟨h1, h2⟩ := rank_step hn hl hp0
    obtain ⟨k', d', hk', hσ', h3, h4, h5⟩ := ih k0 (by omega) (by omega) hσ0 (by omega)
    exact ⟨k', d', by omega, hσ', h3, h4, h5⟩

/-! ### Progress -/

/-- **The loader reaches every site after `ldb0` of every block it loads.** A thread of warp 6
that exited and led its elections has, for each iteration `num_pre ≤ i < num_iters` and each site
`s` from `ldb0` on, a state at `s` of iteration `i`. -/
theorem loader_reaches (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
    (hn : NumWordRead Q L X) (hw6 : g % L.block / 32 = 6)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) (hlead : ElectLead L g (X.tr g))
    {i0 : Nat} (h1 : ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) ≤ i0)
    (h2 : i0 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) {s : Loader.Site}
    (hs : 3 ≤ pos s) :
    ∃ k d P, k < (X.tr g).length ∧ St Q L X g k = some (some (.w (.loader d P))) ∧
      d.site = s ∧ d.i = i0 := by
  obtain ⟨j, d1, P, hj, hσ1, hs1⟩ := exists_setMaxInc hpre hX hf hR hw6 hex
  have hge := setMaxInc_ge hX hf.ldRng hj hσ1 hs1
  have hn1 : d1.n = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) :=
    (page_inv hpre hX hf hn j _ hσ1).1 (by rw [hs1]; rfl)
  have hps := pos_le s
  have hR1 : 1 ≤ 20 * i0 + pos s := by omega
  have hb : ∀ k d P, St Q L X g k = some (some (.w (.loader d P))) → d.site = .bar0 →
      20 * d.i < 20 * i0 + pos s := by
    intro k d P hσ hbar
    have := Lk.ipre_inv hpre hX hf hp k _ hσ (.inr hbar)
    omega
  have hr1 : 20 * i0 + pos s ≤ rank d1 := by
    rw [rank_eq (by rw [hs1]; rintro (h | h | h) <;> cases h), hs1]
    show _ ≤ 20 * d1.i + 1
    omega
  obtain ⟨k', d', hk', hσ', hr', hnp, hnb⟩ := reach_rank hX hlead hR1 hb j hj hσ1 hr1
  rw [rank_eq hnp] at hr'
  have hp1 := pos_pos hnp hnb
  have hp2 := pos_le d'.site
  by_cases h3 : 3 ≤ pos d'.site
  · have hi : d'.i = i0 := by omega
    have hpos : pos d'.site = pos s := by omega
    exact ⟨k', d', P, by omega, hσ', pos_inj hpos h3, hi⟩
  · exfalso
    omega

/-! ### The thread that leads the elections of warp 6 -/

/-- **A warp has a thread that leads its elections.** For a thread `g0` launched, every lane of its
warp is a launched thread, and one of them, `h`, led every election of its trace. -/
theorem exists_lead (hX : Consistent L kernel asms mem0 X) (hb : L.block = 256)
    {g0 : Nat} (hg0 : g0 < L.threads) :
    ∃ h, SameWarp L g0 h ∧ ElectLead L h (X.tr h) := by
  have hlane : ∀ l, l < 32 → ∃ h, SameWarp L g0 h ∧ laneOf L h = l := by
    intro l hl
    refine ⟨g0 - laneOf L g0 + l, ?_, ?_⟩
    · have hth : L.threads = L.grid * L.block := rfl
      unfold laneOf
      refine ⟨⟨hg0, ?_, ?_⟩, ?_⟩
      · rw [hth, hb] at hg0 ⊢
        omega
      · rw [hb]; omega
      · rw [hb]; omega
    · unfold laneOf
      rw [hb]
      omega
  by_cases hl : ElectLead L g0 (X.tr g0)
  · exact ⟨g0, ⟨⟨hg0, hg0, rfl⟩, rfl⟩, hl⟩
  · have hel : ∃ ld, Elected (X.tr g0) ld := by
      by_contra hne
      push Not at hne
      exact hl (electLead_of_not_elected hne).1
    obtain ⟨ld, hld⟩ := hel
    obtain ⟨h, -, hw, hlh⟩ := exists_leader hX.elect hld hlane
    refine ⟨h, hw, fun e he mask inst ld' hk => ?_⟩
    have := leader_eq hX.elect (.inr hw) (electMask_full hX g0) (electMask_full hX h) hld
      ⟨e, he, mask, inst, hk⟩
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
