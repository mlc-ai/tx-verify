-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixWeak
public import Kernels.InklingRelDecode.Proof.Interface.BaseWRead
public import Kernels.InklingRelDecode.Proof.Interface.ClassSm
public import Kernels.InklingRelDecode.Proof.Interface.TmCode

@[expose] public section

/-!
# No base-word stop is taken

If every read of the Tensor Memory base word returns the zero word (`BaseWordRead`), no thread
reaches a base-word stop (`BaseStop`): along a followed thread the word a default-partition state
holds is `b32 0` (`tmz_inv_at`), so the prologue's last event sees a good word; and the word a
worker inherits is `b32 0` (`wz_inv_at`), so the dispatch into the MMA role sees a good word.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Bar

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The base word a worker state inherited is the zero word** (after the worker's load). -/
def WZ : TSt → Prop
  | .w (.worker w) => (w.site ≠ .bar0 ∧ w.site ≠ .ld0) → w.P.rest 463 = b32 0
  | .w (.idle d) => d.P.rest 463 = b32 0
  | .w (.loader _ P) => P.rest 463 = b32 0
  | .w (.mma _ P) => P.rest 463 = b32 0
  | _ => True

theorem handoff_463 {g : Nat} (P : Loader.Pro) :
    (WComp.handoffPro L g P).rest 463 = P.rest 463 := by
  simp [WComp.handoffPro, Worker.handoff, Worker.valueOf, Worker.own, Loader.Pro.val,
    Loader.Pro.table, List.lookup]

theorem bump_463 (P : Loader.Pro) : (Worker.bumpPro P).rest 463 = P.rest 463 := by
  simp [Worker.bumpPro, Worker.roundReg]

/-- **A step keeps `WZ`**, when the worker's load of the base word reads the zero word. -/
theorem wz_next {g : Nat} {s s' : TSt} {e : Event}
    (hz : ∀ (P : Loader.Pro) a bs, s = .w (.worker ⟨.ld0, P⟩) → e.kind = .rd a bs →
      bs = (b32 0).toBytes.map some)
    (h : WZ s) (hn : (threadCode L g Q).next s e = some (some s')) : WZ s' := by
  cases s with
  | d s =>
    obtain ⟨a, -, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from hn)
    trivial
  | w s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some s') from hn)
    cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      cases site with
      | ldRole =>
        have h0 : P.rest 463 = b32 0 := h ⟨by simp, by simp⟩
        change WComp.dispatch L g P e = some (some a) at ha
        unfold WComp.dispatch at ha
        split at ha
        · rename_i d' _
          unfold WComp.roleStart at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst ha
            show (WComp.handoffPro L g P).rest 463 = b32 0
            rw [handoff_463, h0]
          · split at ha
            · split at ha
              · simp only [Option.some.injEq] at ha
                subst ha
                show (WComp.handoffPro L g P).rest 463 = b32 0
                rw [handoff_463, h0]
              · cases ha
            · cases ha
          · simp only [Option.some.injEq] at ha
            subst ha
            exact h0
          · simp only [Option.some.injEq] at ha
            subst ha
            trivial
          · simp only [Option.some.injEq] at ha
            subst ha
            exact fun _ => h0
          · cases ha
        · cases ha
        · cases ha
      | ld0 =>
        change (Worker.next L g ⟨.ld0, P⟩ e).map (Option.map .worker) = some (some a) at ha
        obtain ⟨b, hb, rfl⟩ := map_map_eq_some_some ha
        obtain ⟨pc, kd⟩ := e
        cases kd <;> simp [Worker.next] at hb
        rename_i acc bs
        have hbs := hz P acc bs rfl rfl
        subst hbs
        simp only [rebuild_b32] at hb
        obtain rfl := Option.some.inj (Option.some.inj hb)
        intro _
        simp [Worker.setTm]
      | bar0 =>
        change (Worker.next L g ⟨.bar0, P⟩ e).map (Option.map .worker) = some (some a) at ha
        obtain ⟨b, hb, rfl⟩ := map_map_eq_some_some ha
        simp only [Worker.next, Option.some.injEq] at hb
        subst hb
        intro h'
        exact absurd rfl h'.2
      | _ =>
        have h0 : P.rest 463 = b32 0 := h ⟨by simp, by simp⟩
        simp only [WComp.next] at ha
        obtain ⟨b, hb, rfl⟩ := map_map_eq_some_some ha
        simp only [Worker.next] at hb
        repeat' split at hb
        all_goals first
          | (simp at hb; done)
          | (simp only [Option.some.injEq] at hb; subst hb; exact fun _ => h0)
    | idle d =>
      change (match d.site with
        | .inc => some (some (.worker ⟨.loop, Worker.bumpPro d.P⟩))
        | _ => (Worker.Idle.next d e).map (Option.map .idle)) = some (some a) at ha
      split at ha
      · simp only [Option.some.injEq] at ha
        subst ha
        exact fun _ => by rw [bump_463]; exact h
      · obtain ⟨b, hb, rfl⟩ := map_map_eq_some_some ha
        simp only [Worker.Idle.next] at hb
        repeat' split at hb
        all_goals first
          | (simp at hb; done)
          | (simp only [Option.some.injEq] at hb; subst hb; exact h)
    | loader d P =>
      change (match d.site with
        | .setMaxInc => some (some (.worker ⟨.loop, Worker.bumpPro P⟩))
        | _ => (Loader.next L g d e).map (Option.map (fun d' => .loader d' P))) =
        some (some a) at ha
      split at ha
      · simp only [Option.some.injEq] at ha
        subst ha
        exact fun _ => by rw [bump_463]; exact h
      · obtain ⟨b, -, rfl⟩ := map_map_eq_some_some ha
        exact h
    | mma d P =>
      change (match d.site with
        | .setMaxRegInc => some (some (.worker ⟨.loop, Worker.bumpPro P⟩))
        | _ => (Mma.next L g d e).map (Option.map (fun d' => .mma d' P))) =
        some (some a) at ha
      split at ha
      · simp only [Option.some.injEq] at ha
        subst ha
        exact fun _ => by rw [bump_463]; exact h
      · obtain ⟨b, -, rfl⟩ := map_map_eq_some_some ha
        exact h
    | exit x =>
      obtain ⟨site, P⟩ := x
      cases site <;> simp only [WComp.next, Option.some.injEq, reduceCtorEq] at ha
      subst ha
      trivial

/-! ### Reads of the base word and the states along a thread -/

/-- **Every read at a base-read state returns the zero word.** -/
def BaseReadsZero (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)},
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → BaseReadAt Q L X g k → bs = (b32 0).toBytes.map some

/-- `BaseReadsZero` from the tracking up to the base-word stops and the writer facts. -/
theorem baseReadsZero_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hW : WeakTracked Q L X)
    (hB : BaseSources Q L X) : BaseReadsZero Q L X := by
  intro g k pc a bs hget hb
  have hg : g < L.threads := Frame.lt_of_get hX hget
  rcases hb with ⟨tm, hσ⟩ | ⟨P, hσ⟩
  · obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg hget hσ (by simp [ExitState])
    obtain ⟨ac, bs', he2, hl, hz, -⟩ := DStart.shape_ld0 (ProA.sharedOk_of_pre hpre)
      (fired_dstart hF) rfl
    simp only [Event.mk.injEq, Kind.rd.injEq] at he2
    obtain ⟨-, rfl, rfl⟩ := he2
    exact base_read_w hpre hX hS hT hW hB hget (Or.inl ⟨tm, hσ⟩) hl hz
  · obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg hget hσ (by simp [ExitState])
    obtain ⟨t, hgd, hfire⟩ := hF
    obtain ⟨pc', ac, bs', he2, hl, hsz⟩ := worker_ld0_shape hpre (g := g) (w := ⟨.ld0, P⟩) rfl
      ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
    simp only [Event.mk.injEq, Kind.rd.injEq] at he2
    obtain ⟨-, rfl, rfl⟩ := he2
    exact base_read_w hpre hX hS hT hW hB hget (Or.inr ⟨P, hσ⟩) hl hsz

/-- A property kept by every step whose read at a base-read state returns the zero word holds at
every followed state of a thread. -/
theorem inv_along (hz : BaseReadsZero Q L X)
    (Pr : TSt → Prop) {g : Nat} (h0 : Pr (code L Q g).init)
    (hstep : ∀ {k s s' e}, St Q L X g k = some (some s) → (X.tr g)[k]? = some e →
      (∀ a bs, e.kind = .rd a bs → BaseReadAt Q L X g k → bs = (b32 0).toBytes.map some) →
      Pr s → (threadCode L g Q).next s e = some (some s') → Pr s') :
    ∀ k s, St Q L X g k = some (some s) → Pr s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hσ
    by_cases hinit : s = (code L Q g).init
    · subst hinit
      exact h0
    · obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := stateAt_pred hσ hinit
      refine hstep hs0 he (fun a bs hk hb => ?_) (ih k0 hlt s0 hs0) hn
      obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      exact hz he hb

/-! ### No base-word stop is taken -/

/-- **No thread reaches a base-word stop** when every read at a base-read state returns the zero
word. -/
theorem no_baseStop (hz : BaseReadsZero Q L X)
    {g k : Nat} {s : TSt} (hσ : St Q L X g k = some (some s)) : ¬ BaseStop s := by
  have hT : TmZ s := by
    refine inv_along hz TmZ tmz_init (fun hs he hr h hn => ?_) k s hσ
    exact tmz_next (fun tm a bs hs' hk => hr a bs hk (Or.inl ⟨tm, hs' ▸ hs⟩)) h hn
  have hZ : WZ s := by
    refine inv_along hz WZ ?_ (fun hs he hr h hn => ?_) k s hσ
    · show WZ (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init)
      split_ifs
      · trivial
      · intro h
        exact absurd rfl h.1
    · exact wz_next (fun P a bs hs' hk => hr a bs hk (Or.inr ⟨P, hs' ▸ hs⟩)) h hn
  intro hb
  cases s with
  | d s =>
    cases s with
    | pro d =>
      obtain ⟨-, hw⟩ := hb
      obtain ⟨h1, h2⟩ := hT
      simp [ProA.wGood, h1, h2] at hw
    | _ => exact hb.elim
  | w s =>
    cases s with
    | worker w =>
      obtain ⟨hs, hok⟩ := hb
      apply hok
      have h0 : w.P.rest 463 = b32 0 := hZ ⟨by rw [hs]; decide, by rw [hs]; decide⟩
      exact ⟨0, by rw [h0]; rfl, by norm_num⟩
    | _ => exact hb.elim

/-! ### Every followed state is `Discharged` or a base-word stop -/

/-- **No step of a thread's machine enters a role-entry site of the worker machine** (the
dispatch turns them into the roles' first states). -/
theorem next_not_to {g : Nat} {s : TSt} {e : Event} {w : Worker.D}
    (h : (threadCode L g Q).next s e = some (some (.w (.worker w)))) :
    w.site ≠ .toIdle ∧ w.site ≠ .toLoader ∧ w.site ≠ .toMma ∧ w.site ≠ .toExit := by
  cases s with
  | d s =>
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some (.w (.worker w))) from h)
    cases ha
  | w s =>
    obtain ⟨a, ha, h2⟩ := map_map_eq_some_some (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some (.w (.worker w))) from h)
    cases h2
    cases s with
    | worker v =>
      obtain ⟨site, P⟩ := v
      revert ha
      cases site <;>
        simp only [WComp.next, WComp.dispatch, WComp.roleStart, Worker.next, Option.map] <;>
        (repeat' split) <;> simp_all <;> (try (intro hh; subst hh)) <;> try simp_all
      all_goals
        rename_i hq
        revert hq
        repeat' split
        all_goals simp_all
        all_goals (intro hh; subst hh; simp)
    | idle d =>
      obtain ⟨site, P⟩ := d
      revert ha
      cases site <;> simp [WComp.next, Worker.Idle.next]
      intro hh
      subst hh
      simp
    | loader d P =>
      revert ha
      simp only [WComp.next]
      split <;> simp
      intro hh
      subst hh
      simp
    | mma d P =>
      revert ha
      simp only [WComp.next]
      split <;> simp
      intro hh
      subst hh
      simp
    | exit x =>
      obtain ⟨site, P⟩ := x
      revert ha
      cases site <;> simp [WComp.next]

/-- **A followed state is `Discharged` or a base-word stop.** -/
theorem discharged_or_stop (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hX : Consistent L kernel asms mem0 X) {g k : Nat} {s : TSt} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    Discharged s ∨ BaseStop s := by
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX he hσ
  cases s with
  | d s =>
    cases s with
    | dstart d =>
      left
      have hne : d.site ≠ .toProA := hinv.2.2
      by_cases hs : d.site = .shfl
      · exact .inr hs
      · exact .inl ⟨hs, hne⟩
    | pro d =>
      by_cases hb : d.site = .bar18
      · cases hw : ProA.wGood d.dt
        · exact .inr ⟨hb, hw⟩
        · exact .inl (.inr (.inr (.inr (.inl ⟨hb, hw⟩))))
      · left
        cases hm : ProA.mayLeave d.site
        · exact .inr (.inr (.inr (.inr (.inr (.inr hm)))))
        · simp only [ProA.mayLeave, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
          rcases hm with ((((h | h) | h) | h) | h) | h
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inl h))
          · exact absurd h hb
          · exact .inr (.inr (.inr (.inr (.inl (ProA.ldqSites_idx h)))))
          · exact .inr (.inr (.inr (.inr (.inr (.inl (ProA.lbSites_idx h))))))
    | sm d =>
      left
      obtain ⟨site, -⟩ := d
      cases site <;> simp [Discharged, DComp.smMayLeave]
    | epi _ => exact .inl trivial
  | w s =>
    cases s with
    | worker w =>
      have hnt : w.site ≠ .toIdle ∧ w.site ≠ .toLoader ∧ w.site ≠ .toMma ∧
          w.site ≠ .toExit := by
        by_cases hinit : TSt.w (.worker w) = (code L Q g).init
        · have hd : ¬ g % L.block < 128 := hinv.1
          have : (code L Q g).init = .w (WComp.code L g Q).init := by
            show (if g % L.block < 128 then _ else _) = _
            simp [hd]
          rw [this] at hinit
          cases hinit
          simp [Worker.D.start]
        · obtain ⟨k0, e0, s0, -, -, -, hn⟩ := stateAt_pred hσ hinit
          exact next_not_to hn
      obtain ⟨site, P⟩ := w
      obtain ⟨h1, h2, h3, h4⟩ := hnt
      by_cases hr : site = .ldRole
      · subst hr
        by_cases hok : WComp.baseOk P
        · exact .inl (.inr (.inr ⟨rfl, hok⟩))
        · exact .inr ⟨rfl, hok⟩
      · left
        cases site <;> simp_all [Discharged]
    | idle _ => exact .inl trivial
    | loader _ _ => exact .inl trivial
    | mma _ _ => exact .inl trivial
    | exit _ => exact .inl trivial

/-- **The machines follow every thread** in every consistent execution, given the writer facts
of the base word on the tracking up to the base-word stops: every followed state that is not
`Discharged` is a base-word stop (`discharged_or_stop`), so the machines follow every thread up to
its base-word stop (`weakTracked_of`), the base reads return the zero word (`baseReadsZero_of`),
and no thread reaches a stop (`no_baseStop`). -/
theorem tracked_of_close (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hBS : WeakTracked Q L X → BaseSources Q L X) : Frame.Tracked (code L Q) X := by
  have hS := sound_all hpre smOb
  have hT := tmplOk hpre
  have hW : WeakTracked Q L X := weakTracked_of hpre hX hS hT
    (fun g k s e hg he hσ hd hb _ _ => absurd ((discharged_or_stop hS hX he hσ).resolve_left hd) hb)
  have hz : BaseReadsZero Q L X := baseReadsZero_of hpre hX hS hT hW (hBS hW)
  exact tracked_of_weak hW fun _ _ _ _ hσ => no_baseStop hz hσ

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
