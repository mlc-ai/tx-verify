-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxEvents
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Lemmas.Flow.NotTcData
public import Lemmas.Flow.NotTcSt
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The output stages' polls and arrivals, over every role

`OutputFacts.staged_poll` and `OutputFacts.free_arrive`: the store warp's polls and arrivals
(`Facts.Store.staged_poll`, `Facts.Store.free_arrive`), and no other role polls a staged barrier
or arrives on a free barrier. An event of a role state is its site's event (`role_event`): the
loader polls ring empty barriers and arrives on ring full barriers (`Loader.wait_fact`,
`Loader.arrive_fact`); the MMA warp polls its sites' barriers and arrives on the peer's handshake
barrier (`wait_ev`, `arrive_ev`); the softmax warps poll the statistics credit and S-full
barriers and arrive on the leader's P-ready barriers (`Softmax.Ev`); the correction warps poll
O-full, free and the last free barrier and arrive on credit, staged and the leader's O-free
barriers (`corr_wait`, `corr_arrive`); the idle warp has no poll or arrival site. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The idle warp has no poll and no arrival site. -/
theorem Idle.site_not_poll (s : Idle.Site) :
    s.pc ∉ Flow.mbarWait.toList ∧ s.pc ∉ Flow.mbarArrive.toList := by
  cases s <;> site_decide

/-- **An event of a kind the prologue does not fire, that does not end its thread**, is fired
by a role state with the role's run invariant, and continues. -/
theorem role_event (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hend : ¬ Ends e) (hpk : ¬ Prologue.ProKind e.kind) :
    ∃ r t ins u, Frame.stateAt (code L) X g k = some (some (.inr r)) ∧
      roleJ L g (.inr r) ((X.tr g).take k) ∧ (code L g).AtD (.inr r) t ∧
      (code L g).inv (.inr r) ∧ kernel.code[(code L g).pc (.inr r)]? = some ins ∧
      Fires ((code L g).pc (.inr r)) (eventTmpl asms L g t ins.op) e (some u) := by
  obtain ⟨d, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    Cross.event_cont hpre hX ht (fun g hg => roleJ_run hpre hg) he hend
  rcases d with p | r
  · exact absurd (pro_event hpre hX he hσ fun f h => hend (.inl ⟨f, h⟩)).proKind hpk
  · exact ⟨r, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩

/-- A Tensor Memory load or store of a shape other than `.32x32b`, or a reducing load. -/
def tcOtherShapeOp : Op → Bool
  | .tcLd _ _ sh red => decide (sh ≠ .s32x32b) || red.isSome
  | .tcSt _ _ sh => decide (sh ≠ .s32x32b)
  | _ => false

/-- Every Tensor Memory load and store of the kernel has the shape `.32x32b`. -/
theorem kernel_tc_shape : OpPcsFast kernel.code tcOtherShapeOp [] = true := by
  decide +kernel

/-- A load template's event has the instruction's shape. -/
theorem fires_tcTmpl_shape {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (tcTmpl L g t (.tcLd ds ta sh)) e o) {a : Nat} {vals : List Value}
    {sh' : TcShape} (he : e.kind = .tc (.ld a vals sh')) : sh' = sh := by
  cases sh <;> simp only [tcTmpl] at hf <;>
    cases ha : readBits L g t 32 (.reg ta) <;>
    simp [ofExec, ha, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨rfl, -⟩ := hf; simp at he)
    | (obtain ⟨vals', -, rfl, -⟩ := hf
       simp only [Kind.tc.injEq, TcKind.ld.injEq] at he
       exact he.2.2.symm)

/-- A Tensor Memory load's event has the instruction's shape. -/
theorem fires_tcLd_shape {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e o) {a : Nat} {vals : List Value}
    {sh' : TcShape} (he : e.kind = .tc (.ld a vals sh')) : sh' = sh := by
  rcases eventTmpl_tcLd_cases (A := A) (L := L) (g := g) (t := t) (ds := ds) (ta := ta)
    (sh := sh) with
    h | h | h <;> rw [h] at hf
  · exact fires_tcTmpl_shape hf he
  · obtain ⟨o', hf⟩ := fires_thenWaitLd hf
    exact fires_tcTmpl_shape hf he
  · obtain ⟨rfl, -⟩ := hf
    cases he

/-- A Tensor Memory store's event has the instruction's shape. -/
theorem fires_tcSt_shape {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} {ta a : Nat} {ss : List Opnd} {sh sh' : TcShape}
    {vals : List Value} (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hk : e.kind = .tc (.st a vals sh') ∨ e.kind = .tc (.ld a vals sh')) : sh' = sh := by
  have ⟨u, _, hf⟩ : ∃ u, u.regs = t.regs ∧ Fires pc (tcTmpl L g u (.tcSt ta ss sh)) e o := by
    rcases hk with h | h
    · exact fires_tcSt_core hf h (by intro h'; cases h')
    · exact fires_tcSt_core hf h (by intro h'; cases h')
  cases sh <;> simp only [tcTmpl] at hf <;>
    cases ha : readBits L g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g u 32) <;>
    simp only [ofExec, ha, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
    simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq, or_false] at hk
  all_goals exact hk.2.2.symm

/-- A `tcgen05` data instruction of shape `.32x32b` fires loads and stores of that shape. -/
theorem fires_tc_shape {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {p pc : Nat} {tk : TcKind} {o : Option TState} {a : Nat} {vals : List Value} {sh : TcShape}
    (hf : Fires p (eventTmpl A L g t op) ⟨pc, .tc tk⟩ o)
    (htk : tk = .ld a vals sh ∨ tk = .st a vals sh) (hop : tcOtherShapeOp op = false) :
    sh = .s32x32b := by
  have hd : tcDataOp op = true := fires_tcData_op hf (by rcases htk with rfl | rfl <;> rfl)
  cases op <;> simp only [tcDataOp, Bool.false_eq_true] at hd
  case tcLd ds ta sh0 red =>
    simp only [tcOtherShapeOp, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rcases htk with rfl | rfl
    · exact fires_tcLd_shape hf rfl
    · have := fires_tcSt_op hf rfl
      simp [tcStOp] at this
  case tcSt ta ss sh0 =>
    simp only [tcOtherShapeOp, decide_eq_false_iff_not, not_not] at hop
    subst hop
    rcases htk with rfl | rfl
    · exact fires_tcSt_shape hf (.inr rfl)
    · exact fires_tcSt_shape hf (.inl rfl)
  all_goals
    rcases htk with rfl | rfl
    all_goals
      simp only [eventTmpl, tcTmpl] at hf
      simp [ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hf
      split_ifs at hf <;> simp [Fires] at hf

/-- **A Tensor Memory load or store event has the shape `.32x32b`**: it is fired by a site's
instruction, and every `tcgen05.ld` and `tcgen05.st` of the kernel has that shape
(`kernel_tc_shape`). -/
theorem tc_shape_of_get (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} {tk : TcKind} {a : Nat} {vals : List Value}
    {sh : TcShape} (he : X.get (g, k) = some ⟨pc, .tc tk⟩)
    (htk : tk = .ld a vals sh ∨ tk = .st a vals sh) : sh = .s32x32b := by
  obtain ⟨r, t, ins, u, -, -, -, -, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h)
      (by simp [Prologue.ProKind])
  cases hop : tcOtherShapeOp ins.op
  · exact fires_tc_shape hf htk hop
  · have := OpPcsFast.mem kernel_tc_shape hc hop
    simp at this

theorem stagedBar_fbar (L : Launch) (c : Nat) {st : Nat} (hst : st < 2) :
    stagedBar L c st = FBar.loc L c (.oStaged ⟨st, hst⟩) :=
  stagedBar_eq L c ⟨st, hst⟩

theorem freeBar_fbar (L : Launch) (c : Nat) {st : Nat} (hst : st < 2) :
    freeBar L c st = FBar.loc L c (.oFree ⟨st, hst⟩) :=
  freeBar_eq L c ⟨st, hst⟩

/-- **Every poll of a staged barrier is a store lane's of the barrier's CTA**, with the parity
of its earlier successful polls of the barrier; a poll acquires. -/
theorem OutputFacts_staged_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      st < 2 → X.get (g, i) = some ⟨pc, .wait (stagedBar L c st) p ok acq sc⟩ →
        warpOf L g = 13 ∧ c = ctaOf L g ∧
        p % 2 = okPolls (stagedBar L c st) ((X.tr g).take i) % 2 ∧ (ok = true → acq = true) := by
  intro g i pc p c st ok acq sc hg hst he
  obtain ⟨r, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h) (fun h => h)
  have hw := Cross.role_of_state hpre hX hg hσ
  have hk : (⟨pc, .wait (stagedBar L c st) p ok acq sc⟩ : Event).kind =
      .wait (stagedBar L c st) p ok acq sc := rfl
  cases r with
  | store d => exact Facts.Store.staged_poll hpre hX ht hg hw hst he
  | loader d =>
    exfalso
    obtain ⟨b, hb, hm, -⟩ := Loader.wait_fact hpre hg hJ hi
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf hk
    rw [stagedBar_fbar L c hst] at hm
    obtain ⟨rfl, -⟩ := FBar.loc_inj hm
    simp [FBar.isEmpty] at hb
  | mma d =>
    exfalso
    obtain ⟨B, hpb, hm, -⟩ := wait_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hf) hk
    rw [stagedBar_fbar L c hst] at hm
    obtain ⟨hB, -⟩ := FBar.loc_inj hm
    subst hB
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hpb
  | softmax d =>
    exfalso
    have hev := Softmax.site_event hpre hg hi hat hc hf
    have hw8 := hi.warp
    obtain ⟨site, i', tt, sc', m', l'⟩ := d
    cases site <;> simp [Softmax.Ev, stagedBar, Softmax.stOf, Softmax.sb] at hev <;> omega
  | corr d =>
    exfalso
    obtain ⟨hw8, hw12⟩ := hw
    obtain ⟨d', -, -, -, -, h⟩ := corr_wait hpre hX ht hw8 hw12 he
    rcases h with ⟨st', -, hm, -⟩ | ⟨st', -, hm, -⟩ | ⟨-, hm, -⟩ <;>
      simp only [stagedBar, Correction.ownLoc, Correction.sb, Loc.mk.injEq] at hm <;> omega
  | idle s =>
    exfalso
    obtain ⟨p', b, off, par, sc0, hop, -⟩ := fires_wait_flags hf hk
    exact (Idle.site_not_poll s.site).1 (OpPcsFast.mem kernel_poll_pcs hc (by rw [hop]; rfl))

/-- **Every arrival on a free barrier is a store lane's of the barrier's CTA**: one release
arrival without transaction bytes, after more successful polls of the stage's staged barrier
than its earlier free arrivals of the stage. -/
theorem OutputFacts_free_arrive (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
      st < 2 → X.get (g, i) = some ⟨pc, .arrive (freeBar L c st) tx cnt rel sc⟩ →
        warpOf L g = 13 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
        arrivals (freeBar L c st) ((X.tr g).take i) + 1 ≤
          okPolls (stagedBar L c st) ((X.tr g).take i) := by
  intro g i pc tx cnt c st rel sc hg hst he
  obtain ⟨r, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h) (fun h => h)
  have hw := Cross.role_of_state hpre hX hg hσ
  have hk : (⟨pc, .arrive (freeBar L c st) tx cnt rel sc⟩ : Event).kind =
      .arrive (freeBar L c st) tx cnt rel sc := rfl
  cases r with
  | store d => exact Facts.Store.free_arrive hpre hX ht hg hw hst he
  | loader d =>
    exfalso
    obtain ⟨b, hb, hm, -⟩ := Loader.arrive_fact hpre hg hJ hi
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf hk
    rw [freeBar_fbar L c hst] at hm
    obtain ⟨rfl, -⟩ := FBar.loc_inj hm
    simp [FBar.isFull] at hb
  | mma d =>
    exfalso
    obtain ⟨-, hm, -⟩ := arrive_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hf) hk
    rw [freeBar_fbar L c hst] at hm
    exact absurd (FBar.loc_inj hm).1 (by simp)
  | softmax d =>
    exfalso
    have hev := Softmax.site_event hpre hg hi hat hc hf
    obtain ⟨site, i', tt, sc', m', l'⟩ := d
    have hw8 := hi.warp
    cases site <;> simp [Softmax.Ev, freeBar, Softmax.stOf, Softmax.sb] at hev <;> omega
  | corr d =>
    exfalso
    obtain ⟨hw8, hw12⟩ := hw
    obtain ⟨-, -, d', -, -, -, -, h⟩ := corr_arrive hpre hX ht hw8 hw12 he
    rcases h with ⟨a, -, hm⟩ | ⟨st', -, hm⟩ | ⟨st', -, hm⟩ <;>
      simp only [freeBar, Correction.ownLoc, Correction.leadLoc, Correction.sb,
        Loc.mk.injEq] at hm <;> omega
  | idle s =>
    exfalso
    obtain ⟨b, off, tx', c', cl, sc0, st', hop, -⟩ := fires_arrive_flags hf hk
    exact (Idle.site_not_poll s.site).2 (OpPcsFast.mem kernel_arrive_pcs hc (by rw [hop]; rfl))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
