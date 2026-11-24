-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuBar0f

@[expose] public section

/-!
# A post site follows a last-generation arrival

`PostSite` states (the epilogue's `dealloc` and `exit`, the exit role's `ret`) are reached only
from a final site or another post site (`post_pred`). So a thread at a post site has made a
last-generation arrival (`post_seen`): its event at the final site is a `bar.sync 0` without a
count, after at least two barrier-0 events (`final_event`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger PTX.Kernels.InklingRelDecode.Proof.BarOrd
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem stores_ne (d : Epi.D) : d.stores ≠ .dealloc ∧ d.stores ≠ .exit := by
  unfold Epi.D.stores
  split_ifs <;> simp

theorem stNext_ne (d : Epi.D) (k : Fin 64) :
    (Epi.stNext d k).site ≠ .dealloc ∧ (Epi.stNext d k).site ≠ .exit := by
  unfold Epi.stNext
  split_ifs <;> simp

/-- The epilogue's `dealloc` and `exit` follow its `bar3` or `dealloc`. -/
theorem epi_next_post {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d'))
    (hp : d'.site = .dealloc ∨ d'.site = .exit) : d.site = .bar3 ∨ d.site = .dealloc := by
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> simp only [Epi.next] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    all_goals first
      | (simp at hp; done)
      | (simp; done)
      | (exfalso
         simp only at hp
         rcases hp with hp | hp
         · exact (stores_ne _).1 hp
         · exact (stores_ne _).2 hp)
      | (exfalso
         rcases hp with hp | hp
         · exact (stNext_ne _ _).1 hp
         · exact (stNext_ne _ _).2 hp)

/-- The predecessor of a post site of the default partition is a final or a post site. -/
theorem post_pred_d {L : Launch} {g : Nat} {Q : Params} {s0 a : DComp.St} {e : Event}
    (h : DComp.next L g Q s0 e = some (some a)) (hp : PostSite (.d a)) :
    FinalSite (.d s0) ∨ PostSite (.d s0) := by
  cases s0 with
  | dstart d =>
    obtain ⟨b, hb, hf⟩ := Bound.map_inv (show (DStart.next L g d e).map (Option.map _) =
      some (some a) from h)
    by_cases hs : b.site = DStart.Site.toProA
    · simp only [hs, eq_self, ↓reduceIte] at hf
      subst hf
      simp [PostSite] at hp
    · simp only [hs, ↓reduceIte] at hf
      subst hf
      simp [PostSite] at hp
  | pro d =>
    have h1 : (if d.site = ProA.Site.bar18 then
        (if ProA.WordsMatch Q (ProA.cta L g .z) d.dt ∧ ProA.wGood d.dt = true then
          some (some (DComp.St.sm (SmEntry.d0 (SmEntry.entOf Q L g d.dt)))) else some none)
        else (ProA.next L g d e).map (Option.map DComp.St.pro)) = some (some a) := h
    by_cases hs : d.site = ProA.Site.bar18
    · simp only [hs, eq_self, ↓reduceIte] at h1
      split at h1
      · simp only [Option.some.injEq] at h1
        subst h1
        simp [PostSite] at hp
      · simp at h1
    · simp only [hs, ↓reduceIte] at h1
      obtain ⟨b, hb, rfl⟩ := Bound.map_inv h1
      simp [PostSite] at hp
  | sm d =>
    have h1 : (if DComp.leaves L g d e then DComp.exitNext L g d
        else (Sm.next L g d e).map (Option.map DComp.St.sm)) = some (some a) := h
    by_cases hl : DComp.leaves L g d e
    · simp only [hl, ↓reduceIte] at h1
      have h2 : (if (DComp.exitIn L g d).NoFault then
          some (some (DComp.St.epi (if (DComp.exitIn L g d).skip then
            Epi.D.startSk (Br.prm (DComp.exitIn L g d))
            else Epi.D.start (Br.prm (DComp.exitIn L g d))))) else none) = some (some a) := h1
      split at h2
      · simp only [Option.some.injEq] at h2
        subst h2
        split_ifs at hp <;> simp [PostSite, Epi.D.startSk, Epi.D.start, Epi.D.entry] at hp
      · simp at h2
    · simp only [hl, ↓reduceIte] at h1
      obtain ⟨b, hb, rfl⟩ := Bound.map_inv h1
      simp [PostSite] at hp
  | epi d =>
    obtain ⟨b, hb, rfl⟩ := Bound.map_inv (show (Epi.next d e).map (Option.map DComp.St.epi) =
      some (some a) from h)
    simp only [PostSite] at hp
    have := epi_next_post hb hp
    simp only [FinalSite, PostSite]
    rcases this with h | h
    · exact .inl h
    · exact .inr (.inl h)

theorem dispatch_exit {L : Launch} {g : Nat} {P0 : Loader.Pro} {e : Event} {x : WComp.ExitD}
    (h : WComp.dispatch L g P0 e = some (some (.exit x))) : x.site = .bar := by
  unfold WComp.dispatch at h
  split at h
  · rename_i d' hd
    unfold WComp.roleStart at h
    cases hs : d'.site <;> simp only [hs] at h <;> (repeat' split at h) <;>
      first
      | (simp at h; done)
      | (simp only [Option.some.injEq, WComp.WSt.exit.injEq] at h
         subst h
         rfl)
  · simp at h
  · simp at h

/-- The predecessor of a post site of a worker is a final or a post site. -/
theorem post_pred_w {L : Launch} {g : Nat} {s0 a : WComp.WSt} {e : Event}
    (h : WComp.next L g s0 e = some (some a)) (hp : PostSite (.w a)) :
    FinalSite (.w s0) ∨ PostSite (.w s0) := by
  cases s0 with
  | worker w =>
    by_cases hs : w.site = .ldRole
    · obtain ⟨site0, P0⟩ := w
      simp only at hs
      subst hs
      have h1 : WComp.dispatch L g P0 e = some (some a) := h
      cases a with
      | exit x =>
        have := dispatch_exit h1
        simp [PostSite, this] at hp
      | _ => simp [PostSite] at hp
    · rw [Wt.next_worker_eq hs] at h
      obtain ⟨b, hb, rfl⟩ := Ledger.mapInv h
      simp [PostSite] at hp
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P0⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h1
      subst h1
      simp [PostSite] at hp
    · rw [Wt.next_idle_eq hs] at h
      obtain ⟨b, hb, rfl⟩ := Ledger.mapInv h
      simp [PostSite] at hp
  | loader d P0 =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h1
      subst h1
      simp [PostSite] at hp
    · rw [Wt.next_loader_eq P0 hs] at h
      obtain ⟨b, hb, rfl⟩ := Ledger.mapInv h
      simp [PostSite] at hp
  | mma d P0 =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h1
      subst h1
      simp [PostSite] at hp
    · rw [Wt.next_mma_eq P0 hs] at h
      obtain ⟨b, hb, rfl⟩ := Ledger.mapInv h
      simp [PostSite] at hp
  | exit x =>
    obtain ⟨s, P0⟩ := x
    cases s
    · exact .inl rfl
    · have h1 : (none : Option (Option WComp.WSt)) = some (some a) := h
      cases h1

theorem final_tLb {s : TSt} (hf : FinalSite s) : tLb s = 2 := by
  cases s with
  | d s0 =>
    cases s0 with
    | epi d => rfl
    | _ => exact absurd hf (by simp [FinalSite])
  | w s0 =>
    cases s0 with
    | worker w =>
      simp only [FinalSite] at hf
      simp [tLb, wLb, hf]
    | exit x => rfl
    | _ => exact absurd hf (by simp [FinalSite])

/-- **The event at a final site is the `bar.sync 0` without a count.** -/
theorem final_event (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) (hs : FinalSite s) :
    ∃ pc, e = ⟨pc, .bar 0 none .sync⟩ := by
  have h1 : b0At (TSt.pc s) = 1 := by
    cases s with
    | d s0 =>
      cases s0 with
      | epi d =>
        simp only [FinalSite] at hs
        show b0At d.site.pc = 1
        rw [hs]
        simpa using epi_b0 Epi.Site.bar3
      | _ => exact absurd hs (by simp [FinalSite])
    | w s0 =>
      cases s0 with
      | worker w =>
        simp only [FinalSite] at hs
        show b0At w.site.pc = 1
        rw [hs]
        simpa using worker_b0 Worker.Site.toExit
      | exit x =>
        simp only [FinalSite] at hs
        show b0At x.site.pc = 1
        rw [hs]
        simpa using exit_b0 WComp.ExitSite.bar
      | _ => exact absurd hs (by simp [FinalSite])
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  unfold b0At at h1
  rw [hc'] at h1
  simp only at h1
  split at h1
  · rename_i al hop
    rw [hop] at hf'
    exact ⟨_, EvD.fires_barSync_imm (by decide) hf'⟩
  · omega
  · omega

/-- **A post site follows a last-generation arrival.** -/
theorem post_seen (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {y : Nat} :
    ∀ k s, k ≤ (X.tr y).length → St Q L X y k = some (some s) → PostSite s →
      ∃ j, j < k ∧ FinalArr X 0 2 y j := by
  intro k
  induction k with
  | zero =>
    intro s _ hs hp
    have hs : Frame.stateAt (code L Q) X y 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L y Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    by_cases hd : y % L.block < 128
    · have he : (threadCode L y Q).init = .d (.dstart (DStart.D.start L y)) := by
        show (if y % L.block < 128 then TSt.d (DComp.code L y Q).init
          else .w (WComp.code L y Q).init) = _
        simp only [hd, ite_true]
      rw [he] at hp
      simp [PostSite] at hp
    · have he : (threadCode L y Q).init =
          .w (.worker (Worker.D.start (Worker.startPro Q))) := by
        show (if y % L.block < 128 then TSt.d (DComp.code L y Q).init
          else .w (WComp.code L y Q).init) = _
        simp only [hd, ite_false]
      rw [he] at hp
      simp [PostSite] at hp
  | succ k ih =>
    intro s' hk hs' hp
    have hs'' : Frame.stateAt (code L Q) X y (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr y)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ : Frame.stateAt (code L Q) X y k with
    | none => rw [hσ] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L y Q).next s e = some (some s') := hs''
        have hσ' : St Q L X y k = some (some s) := hσ
        have hpred : FinalSite s ∨ PostSite s := by
          cases s with
          | d s0 =>
            obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L y Q s0 e).map
              (Option.map TSt.d) = some (some s') from hn)
            exact post_pred_d ha hp
          | w s0 =>
            obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L y s0 e).map
              (Option.map TSt.w) = some (some s') from hn)
            exact post_pred_w ha hp
        rcases hpred with hf | hpo
        · obtain ⟨pc, rfl⟩ := final_event hX hS he hσ' hf
          obtain ⟨hlb, -⟩ := ordinal_inv hX hS k s (by omega) hσ'
          have h2 : tLb s = 2 := final_tLb hf
          exact ⟨k, by omega, pc, .sync, he, by omega⟩
        · obtain ⟨j, hj, hfa⟩ := ih s (by omega) hσ' hpo
          exact ⟨j, by omega, hfa⟩

/-- **The time of a final site is `c4`.** -/
theorem final_time (g : Nat) {s : TSt} (hf : FinalSite s) (hto : tTo s = false) :
    time g s = c4 := by
  cases s with
  | d s0 =>
    cases s0 with
    | epi d =>
      simp only [FinalSite] at hf
      simp [time_d, dcompT, epiT, hf, Bound.Epi.siteRank]
      wt_omega
    | _ => exact absurd hf (by simp [FinalSite])
  | w s0 =>
    cases s0 with
    | worker w =>
      simp only [FinalSite] at hf
      simp [tTo, wTo, hf] at hto
    | exit x =>
      simp only [FinalSite] at hf
      simp [time_w, wcompT, exitT, hf]
    | _ => exact absurd hf (by simp [FinalSite])

/-- **`BarTime.lag0f` for `Wt.time`.** -/
theorem bar_lag0f (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) (hub : ¬ HasUb X) {g k pc y : Nat} {d : TSt} (_hg : g < L.threads)
    (hget : X.get (g, k) = some ⟨pc, .bar 0 none .sync⟩)
    (hm : 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0))
    (hσ : St Q L X g k = some (some d)) (hy : y < L.threads) (_hdiv : y / L.block = g / L.block)
    (hno : ∀ j, ¬ FinalArr X 0 2 y j) :
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧
      Sched.threadTime (timed Wt.time Q L) X y ≤ Wt.time g d := by
  obtain ⟨s, hσ', hfs⟩ := final_site hpre hX hS htr hget hm
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  have hto := (phase_inv hpre hX hS hR k d (event_le hget) hσ).1
  have hTg := final_time g hfs hto
  have hnx : ∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hx
    obtain ⟨s, hs⟩ : ∃ s, St Q L X y j = some (some s) :=
      Frame.event_state hS hX htr hx (fun pc f h => by cases h)
    have hp : PostSite s := by
      rcases exit_event_state hX hS htr hx with ⟨e, hσh, hs'⟩ | ⟨x, hσh, hs'⟩
      · rw [hs] at hσh
        obtain rfl := Option.some.inj (Option.some.inj hσh)
        simp [PostSite, hs']
      · rw [hs] at hσh
        obtain rfl := Option.some.inj (Option.some.inj hσh)
        simp [PostSite, hs']
    obtain ⟨j', -, hfa⟩ := post_seen hX hS j s (event_le hx) hs hp
    exact hno j' hfa
  refine ⟨hnx, ?_⟩
  rw [threadTime_unfold]
  rcases end_cases hX hS htr hub hy hnx with ⟨s, hσs, hinv⟩ | ⟨s, e, hlen, hσs, hσn, hinv, he⟩
  · rw [hσs]
    simp only
    have hto' := (phase_inv hpre hX hS hR _ s le_rfl hσs).1
    have hnp : ¬ PostSite s := fun hp => by
      obtain ⟨j', -, hfa⟩ := post_seen hX hS _ s le_rfl hσs hp
      exact hno j' hfa
    rw [hTg]
    exact (c4_bound hinv hto' hnp).1
  · rw [hσn]
    simp only
    rw [hσs]
    simp only
    have hk : (X.tr y).length - 1 ≤ (X.tr y).length := by omega
    have hto' := (phase_inv hpre hX hS hR _ s hk hσs).1
    have hnp : ¬ PostSite s := fun hp => by
      obtain ⟨j', -, hfa⟩ := post_seen hX hS _ s hk hσs hp
      exact hno j' hfa
    have hnf : ¬ FinalSite s := fun hf => by
      obtain ⟨pc1, rfl⟩ := final_event hX hS he hσs hf
      obtain ⟨hlb, -⟩ := ordinal_inv hX hS _ s hk hσs
      have := final_tLb hf
      exact hno _ ⟨pc1, .sync, he, by omega⟩
    have := (c4_bound hinv hto' hnp).2 hnf
    rw [hTg]
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
