-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.InitFacts

@[expose] public section

/-! # The store and idle warps' parts of the warp-level premises

The store warp (13) and the idle warp (15) make no `tcgen05` event (no store or idle site is a
`tcgen05` instruction, `Store.Ev`, `Idle.site_not_tc`; `Cross.hi_no_tc`) and no
named-barrier event (`bar_warp13`). The idle warp makes no arrival and no poll
(`Cross.idle_no_arrive`, `Cross.idle_no_wait`); the store warp's arrivals and polls name its
CTA's free and staged barriers (`Store.Ev`). Hence, for a
thread of warp 13 or 15:

* `Cross.SyncNamed_hi`: its arrivals and polls name barriers of the table of its CTA;
* `Cross.PeerBar2High_hi`: it makes no use of the other CTA;
* `Cross.TcAgree_hi`, `TcExitAgree_hi`, `TcExitAbove_hi`, `BarAgree_hi`: vacuous, or both
  counts zero;
* `Cross.PollAgree_idle`, `Cross.PollRest_idle`: the idle warp has no poll. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem Idle.site_not_tc (s : Idle.Site) : s.pc ∉ Loader.tcPcs := by
  cases s <;> site_decide

theorem Idle.site_not_arrive (s : Idle.Site) : s.pc ∉ Flow.mbarArrive.toList := by
  cases s <;> site_decide

theorem Idle.site_not_wait (s : Idle.Site) : s.pc ∉ Flow.mbarWait.toList := by
  cases s <;> site_decide

/-- Two lanes of one warp are of one warp index. -/
theorem SameWarp.warp_eq {g h : Nat} (hs : SameWarp L g h) : warpOf L h = warpOf L g := by
  have := hs.2
  simp only [warpOf] at this ⊢
  omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **The origin of an idle-warp event**: an event of a thread of warp 15 that the prologue does
not fire is fired at an idle site. -/
theorem Cross.idle_origin {g k : Nat} {e : Event} (hw : warpOf L g = 15)
    (he : X.get (g, k) = some e) (hpk : ¬ Prologue.ProKind e.kind)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ (s : Idle.Site) (t : TState) (ins : Instr) (o : Option TState),
      kernel.code[s.pc]? = some ins ∧ Fires s.pc (eventTmpl asms L g t ins.op) e o := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he hub
  rcases d with p | r
  · refine absurd (pro_event hpre hX he hσ fun f h => hub e.pc f ?_).proKind hpk
    obtain ⟨pc, k⟩ := e
    simp only at h
    subst h
    rfl
  · have hw' := role_of_state hpre hX hg hσ
    cases r with
    | idle s => exact ⟨s.site, t, ins, o, hc, hf⟩
    | _ => simp [Role.kind, RoleKind.Warp, hw] at hw'

/-- A thread of warp 15 makes no arrival. -/
theorem Cross.idle_no_arrive {g k pc : Nat} {m : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope}
    (hw : warpOf L g = 15) : X.get (g, k) ≠ some ⟨pc, .arrive m tx c rel sc⟩ := by
  intro he
  obtain ⟨s, t, ins, o, hc, hf⟩ :=
    Cross.idle_origin hpre hX ht hw he (by simp [Prologue.ProKind]) (fun _ _ h => by cases h)
  obtain ⟨b, off, tx', c', cl, sc0, st, hop, -⟩ := fires_arrive_flags hf rfl
  exact Idle.site_not_arrive s (OpPcsFast.mem kernel_arrive_pcs hc (by rw [hop]; rfl))

/-- A thread of warp 15 makes no poll. -/
theorem Cross.idle_no_wait {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : warpOf L g = 15) : X.get (g, k) ≠ some ⟨pc, .wait m p ok acq sc⟩ := by
  intro he
  obtain ⟨s, t, ins, o, hc, hf⟩ :=
    Cross.idle_origin hpre hX ht hw he (by simp [Prologue.ProKind]) (fun _ _ h => by cases h)
  obtain ⟨p', b, off, par, sc0, hop, -⟩ := fires_wait_flags hf rfl
  exact Idle.site_not_wait s (OpPcsFast.mem kernel_poll_pcs hc (by rw [hop]; rfl))

/-- **A thread of warp 13 or 15 makes no `tcgen05` event.** -/
theorem Cross.hi_no_tc {g k pc : Nat} {kd : TcKind} (hw : warpOf L g = 13 ∨ warpOf L g = 15) :
    X.get (g, k) ≠ some ⟨pc, .tc kd⟩ := by
  intro he
  have hg := Frame.lt_of_get hX he
  have hop : ∀ {op : Op} {t : TState} {pc' : Nat} {o : Option TState},
      Fires pc' (eventTmpl asms L g t op) ⟨pc, .tc kd⟩ o → tcAnyOp op = true := by
    intro op t pc' o hf
    by_contra hne
    exact fires_notTc (by simpa using hne) hf kd rfl
  rcases hw with hw | hw
  · obtain ⟨⟨site, i⟩, -, -, -, hev, -⟩ :=
      Facts.store_ev' hpre hX ht hg hw he (by simp [Prologue.ProKind]) nofun
    cases site <;> simp [Store.Ev] at hev
  · obtain ⟨s, t, ins, o, hc, hf⟩ :=
      Cross.idle_origin hpre hX ht hw he (by simp [Prologue.ProKind]) (fun _ _ h => by cases h)
    exact Idle.site_not_tc s (OpPcsFast.mem Loader.kernel_tc_pcs hc (hop hf))

theorem Cross.hi_tcColl {g k : Nat} {ev : Event} (hw : warpOf L g = 13 ∨ warpOf L g = 15)
    (he : X.get (g, k) = some ev) : isTcColl ev = false := by
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> try rfl
  exact absurd he (Cross.hi_no_tc hpre hX ht hw)

theorem Cross.hi_tcColl_count {g k : Nat} (hw : warpOf L g = 13 ∨ warpOf L g = 15) :
    ((X.tr g).take k).countP isTcColl = 0 := by
  refine List.countP_eq_zero.mpr fun ev hev => ?_
  obtain ⟨j, -, hj⟩ := get_of_mem_take hev
  simp [Cross.hi_tcColl hpre hX ht hw hj]

/-- **`Cross.TcAgree` for warps 13 and 15**: vacuous. -/
theorem Cross.TcAgree_hi {g k pc pc' : Nat} {kd kd' : TcKind}
    (hw : warpOf L g = 13 ∨ warpOf L g = 15) (he : X.get (g, k) = some ⟨pc, .tc kd⟩) :
    pc = pc' ∧ tcStatic kd = tcStatic kd' :=
  absurd he (Cross.hi_no_tc hpre hX ht hw)

/-- **`Cross.TcExitAgree` for warps 13 and 15**: both lanes exit with no `tcgen05` event. -/
theorem Cross.TcExitAgree_hi {g h k k' : Nat} (hw : warpOf L g = 13 ∨ warpOf L g = 15)
    (hs : SameWarp L g h) :
    ((X.tr g).take k).countP isTcColl = ((X.tr h).take k').countP isTcColl := by
  rw [Cross.hi_tcColl_count hpre hX ht hw,
    Cross.hi_tcColl_count hpre hX ht (SameWarp.warp_eq hs ▸ hw)]

/-- **`Cross.TcExitAbove` for warps 13 and 15**: vacuous. -/
theorem Cross.TcExitAbove_hi {g h k k' n : Nat} (hw : warpOf L g = 13 ∨ warpOf L g = 15)
    (hK : X.TcK (g, k) n) : n < ((X.tr h).take k').countP isTcColl := by
  obtain ⟨⟨ev, he, hc⟩, -⟩ := hK
  rw [Cross.hi_tcColl hpre hX ht hw he] at hc
  cases hc

/-- **`Cross.BarAgree` for warps 13 and 15**: vacuous (`bar_warp13`). -/
theorem Cross.BarAgree_hi {g i : Nat} {x y : Event} (hw : 13 ≤ warpOf L g)
    (hx : X.get (g, i) = some x) (hbx : Execution.isBar x = true) : x = y := by
  obtain ⟨pc, kd⟩ := x
  cases kd <;> simp only [Execution.isBar, Bool.false_eq_true] at hbx
  have := Cross.bar_warp13 hpre hX ht hx
  omega

/-- **The store and idle warps' part of `Cross.SyncNamed`**: an arrival or a poll of a thread of
warp 13 names its CTA's free or staged barrier; warp 15 makes neither. -/
theorem Cross.SyncNamed_hi {g k pc : Nat} {m : Loc} {kd : Kind} (hg : g < L.threads)
    (hw : warpOf L g = 13 ∨ warpOf L g = 15) (he : X.get (g, k) = some ⟨pc, kd⟩)
    (hk : (∃ tx c rel sc, kd = .arrive m tx c rel sc) ∨
      (∃ p ok acq sc, kd = .wait m p ok acq sc)) :
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L g / 2 ∧ ∀ i st, b ≠ .spare i st := by
  rcases hw with hw | hw
  · rcases hk with ⟨tx, c, rel, sc, rfl⟩ | ⟨p, ok, acq, sc, rfl⟩
    · obtain ⟨d, -, -, -, hev, -⟩ := Facts.store_ev' hpre hX ht hg hw he id nofun
      obtain ⟨st, -, rfl, -⟩ := Store.ev_arrive hev
      exact ⟨.oFree st, ctaOf L g, by rw [Store.freeAt_eq, freeBar_eq], rfl, nofun⟩
    · obtain ⟨d, -, -, -, hev, -⟩ := Facts.store_ev' hpre hX ht hg hw he id nofun
      obtain ⟨st, -, rfl, -⟩ := Store.ev_wait hev
      exact ⟨.oStaged st, ctaOf L g, by rw [Store.stagedAt_eq, stagedBar_eq], rfl, nofun⟩
  · rcases hk with ⟨tx, c, rel, sc, rfl⟩ | ⟨p, ok, acq, sc, rfl⟩
    · exact absurd he (Cross.idle_no_arrive hpre hX ht hw)
    · exact absurd he (Cross.idle_no_wait hpre hX ht hw)

/-- **The store and idle warps' part of `Cross.PeerBar2High`**: a thread of warp 13 or 15 makes no
use of the other CTA: its arrivals name barriers of its own CTA, and it makes no commit. -/
theorem Cross.PeerBar2High_hi {g k : Nat} {ev : Event} (hg : g < L.threads)
    (hw : warpOf L g = 13 ∨ warpOf L g = 15) (he : X.get (g, k) = some ev) :
    ¬ PeerEvent L g ev := by
  rintro (⟨m, tx, cnt, rel, sc, hk, hne, -⟩ | ⟨sp, hk⟩)
  · obtain ⟨pc, kd⟩ := ev
    simp only at hk
    subst hk
    obtain ⟨b, c, rfl, -, -⟩ := Cross.SyncNamed_hi hpre hX ht hg hw he (.inl ⟨_, _, _, _, rfl⟩)
    rcases hw with hw | hw
    · obtain ⟨d, -, -, -, hev, -⟩ := Facts.store_ev' hpre hX ht hg hw he id nofun
      obtain ⟨st, -, hm, -⟩ := Store.ev_arrive hev
      rw [hm, Store.freeAt_eq] at hne
      exact hne rfl
    · exact Cross.idle_no_arrive hpre hX ht hw he
  · obtain ⟨pc, kd⟩ := ev
    simp only at hk
    subst hk
    exact Cross.hi_no_tc hpre hX ht hw he

/-- **`Cross.PollAgreeRest` for warp 15**: vacuous (the idle warp has no poll). -/
theorem Cross.PollAgree_idle {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    {C : Prop} (hw : warpOf L g = 15) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩) : C :=
  absurd he (Cross.idle_no_wait hpre hX ht hw)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
