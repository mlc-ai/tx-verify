-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerSites
public import Lemmas.Flow.GateCount

@[expose] public section

/-! # The CLC response's polls and acknowledgements, for every role

Every role polls its CTA's CLC response barrier at its CLC poll, with its phase `cp`, and
acknowledges a response it observed by one arrival on the leader CTA's acknowledgement barrier. Each
role's view of the response barrier as a gate (`Prologue.Role.clcView`) says which responses it
holds unacknowledged and with which parity its polls go on. One run invariant over all roles
(`clcInv`) gives each poll's parity and each acknowledgement's budget (`clc_counts`); per role only
its poll and acknowledgement sites and its step are proved. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A held response: from the successful poll to the acknowledgement. -/
def Loader.D.clcView (d : Loader.D) : GateView :=
  let h := match d.site with | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 1 | _ => 0
  ⟨h, 0, d.cp + h,
    match d.site with | .drain _ | .exitArrive | .exitWait | .exit => false | _ => true⟩

def Mma.D.clcView (d : Mma.D) : GateView :=
  let h := match d.site with | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 1 | _ => 0
  let task := match d.site with
    | .clcWait | .elect | .exitArrive | .exitWait | .exit => 0 | _ => 1
  ⟨h, 0, if d.site = .elect then 0 else d.cp + task, !d.site.done⟩

def Scheduler.D.clcView (d : Scheduler.D) : GateView :=
  let h := match d.site with | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 1 | _ => 0
  ⟨h, 0, if d.site = .elect then 0 else d.cp,
    match d.site with | .exitArrive | .exitWait | .exit => false | _ => true⟩

def Consumer.D.clcView (d : Consumer.D) : GateView :=
  let h := match d.site with
    | .clcLoad | .clcStatus | .clcFirst | .clcFence | .clcBar | .ack => 1 | _ => 0
  let task := match d.site with
    | .setMaxReg | .clcWait | .finalDrain | .exitArrive | .exitWait | .relinquish | .ldBase
    | .dealloc | .exit => 0
    | _ => 1
  ⟨h, 0, if d.site = .setMaxReg then 0 else d.cp + task, d.site.looping⟩

/-- Each role's view of its CTA's response barrier as the gate of its acknowledgements. -/
def Prologue.Role.clcView : Prologue.Role → GateView
  | .loader l => l.clcView
  | .mma m => m.clcView
  | .sched s => s.clcView
  | .cons c => c.clcView

/-- Whether a role has passed its proxy fence since its latest response poll: from the fence to
its acknowledgement. -/
def Loader.D.clcFenced (d : Loader.D) : Bool := decide (d.site = .ack)
def Mma.D.clcFenced (d : Mma.D) : Bool := decide (d.site = .ack)
def Scheduler.D.clcFenced (d : Scheduler.D) : Bool := decide (d.site = .ack)
def Consumer.D.clcFenced (d : Consumer.D) : Bool := decide (d.site = .clcBar ∨ d.site = .ack)

def Prologue.Role.clcFenced : Prologue.Role → Bool
  | .loader l => l.clcFenced
  | .mma m => m.clcFenced
  | .sched s => s.clcFenced
  | .cons c => c.clcFenced

/-- A proxy fence event. -/
def isFence (e : Event) : Bool := match e.kind with
  | .fenceProxy (.async (some (.shared .cta))) none => true
  | _ => false

/-- Whether a role acknowledges every response it polls: all but the consumers that are not their
group's first thread. -/
def Prologue.Role.acks (L : Launch) (g : Nat) : Prologue.Role → Bool
  | .cons _ => Consumer.first L g
  | _ => true

/-- The CLC counts along a thread's run: none in the prologue; in a role, the gate relation, a
proxy fence since the latest response poll while the role is fenced, and, for a role that
acknowledges every response, the converse bound of the gate relation. -/
def ClcInv (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, es => Quiet es
  | .inr r, es => GateRel (clcResp L g) (arrivesOn (clcAck L g)) r.clcView es ∧
      MarkRel (clcResp L g) isFence r.clcFenced es ∧
      (r.acks L g = true → LowRel (clcResp L g) (arrivesOn (clcAck L g)) r.clcView es)

/-- A proxy fence instruction fires a proxy fence event. -/
theorem fence_fires {A : List Assumption} {t : TState} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.fence (.proxy (.async (some (.shared .cta)))))) e o) :
    isFence e = true := by
  simp only [eventTmpl, fenceTmpl_asyncCta, Fires] at hf
  rw [hf.1]
  rfl

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Off the CLC poll a step polls the response barrier unsuccessfully, and off the
acknowledgement it does not arrive on the acknowledgement barrier. -/
theorem clc_off {e : Event} {S : Type} {site : S} {poll ack : S} {cp : Nat}
    (hW : ∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc → site = poll ∧ p % 2 = cp % 2)
    (hA : ∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc → site = ack) :
    (site ≠ poll → okPoll (clcResp L g) e = false) ∧
      (site ≠ ack → arrivesOn (clcAck L g) e = false) := by
  refine ⟨fun hs => Bool.eq_false_iff.mpr fun h => hs ?_,
    fun hs => Bool.eq_false_iff.mpr fun h => hs ?_⟩
  · obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
    exact (hW _ _ _ _ hk).1
  · obtain ⟨tx, c, rel, sc, hk⟩ := arrivesOn_form h
    exact hA _ _ _ _ hk

/-- A poll of the response barrier at the CLC poll counts as successful when it succeeds. -/
theorem okPoll_clc {pc p : Nat} {ok acq : Bool} {sc : MbarScope} :
    okPoll (clcResp L g) ⟨pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc⟩ = ok ∧
      arrivesOn (clcAck L g) ⟨pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc⟩ =
        false := by
  rw [okPoll_wait rfl]
  simp [clcResp, Bar.loc, Bar.off, arrivesOn, sourceArrive]

/-- The sweep over a role's successor states after a step, by cases on the site. -/
macro "clc_sweep " hn:ident : tactic => `(tactic| (
  all_goals repeat' (first | split_ifs at $hn:ident | split at $hn:ident)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at $hn:ident)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at $hn:ident
                  obtain ⟨_, -, rfl⟩ := $hn:ident))
  all_goals (try subst $hn:ident)
  all_goals subst_vars))

namespace Loader

set_option maxHeartbeats 4000000 in
/-- The loader polls the response barrier only at its CLC poll, with its phase, and arrives on the
acknowledgement barrier only at its acknowledgement. -/
theorem clc_sites (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc →
      d.site = .clcWait ∧ p % 2 = d.cp % 2) ∧
    (∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc → d.site = .ack) := by
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  refine ⟨fun p ok acq sc hk => ?_, fun tx c rel sc hk => ?_⟩
  · cases hp : site.polls
    · exact (fires_notWait (eventTmpl_notWait (code_notPoll site hp hc)) hf _ _ _ _ _ hk).elim
    cases site <;> simp only [Site.polls, Bool.false_eq_true] at hp
    · obtain ⟨_, _, _, rfl⟩ := wait_event hpre _ rfl hat hc hf
      have := (InputRing.slotOf ‹Fin 8›).isLt
      simp only [Kind.wait.injEq, InputRing.emptyLoc, clcResp, Bar.loc, Bar.off, Loc.mk.injEq] at hk
      omega
    · obtain ⟨p', _, _, _, hp', rfl⟩ := clcWait_event hpre rfl hat hc hf
      simp only [Kind.wait.injEq] at hk
      exact ⟨rfl, hk.2.1 ▸ hp'⟩
    · obtain ⟨_, _, _, rfl⟩ := drain_event hpre _ rfl hat hc hf
      have := (‹Fin 4›).isLt
      simp only [Kind.wait.injEq, InputRing.emptyLoc, clcResp, Bar.loc, Bar.off, Loc.mk.injEq] at hk
      omega
  · cases ha : site.arrives
    · exact (notArrive_fires site ha hc hf _ _ _ _ _ hk).elim
    cases site <;> simp only [Site.arrives, Bool.false_eq_true] at ha
    · obtain ⟨_, _, rfl⟩ := arrive_event hpre hg _ rfl hat hc hf
      have := (InputRing.slotOf ‹Fin 8›).isLt
      simp only [Kind.arrive.injEq, InputRing.fullLoc, clcAck, Bar.loc, Bar.off, Loc.mk.injEq] at hk
      omega
    · rfl

set_option maxHeartbeats 8000000 in
theorem clc_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    GateStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView ∧
      LowStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView := by
  obtain ⟨hW, hA⟩ := clc_sites hpre hg hat hc hf
  obtain ⟨hok, har⟩ := clc_off hW hA
  have hack : d.site = .ack → arrivesOn (clcAck L g) e = true := by
    intro hs
    obtain ⟨tx, c, rel, sc, rfl⟩ := ack_event hpre hg hs hat hc hf
    simp [clcAck, Bar.loc, Bar.off, arrivesOn, sourceArrive]
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  have hcp : cp < 2 := hi.cp
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl hat hc hf
    obtain ⟨h1, h2⟩ := okPoll_clc (L := L) (g := g) (pc := Site.clcWait.pc) (p := p) (ok := ok)
      (acq := acq) (sc := sc)
    simp only [next, Option.some.injEq] at hn
    subst hn
    cases ok <;> simp [GateStep, LowStep, D.clcView, h1, h2]
  all_goals clear hat hc hf hW hA
  all_goals dsimp only at hok har hack
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok har hack
  all_goals simp only [next, endOfTrip] at hn
  clc_sweep hn
  all_goals (simp only [GateStep, LowStep, D.clcView, hok]; try simp only [har])
  all_goals (split_ifs <;> first | (simp_all; done) | (simp_all; omega))

set_option maxHeartbeats 8000000 in
/-- A step into a fenced state is the proxy fence or keeps a fenced state, without a successful
response poll. -/
theorem fence_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next L g d e = some (some d')) :
    d'.clcFenced = true → okPoll (clcResp L g) e = false ∧
      (isFence e = true ∨ d.clcFenced = true) := by
  intro hfen
  obtain ⟨hW, hA⟩ := clc_sites hpre hg hat hc hf
  obtain ⟨hok, -⟩ := clc_off hW hA
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  cases site
  case clcFence =>
    code_at hc
    subst hc
    exact ⟨hok (by simp), .inl (fence_fires hf)⟩
  all_goals clear hat hc hf hW hA
  all_goals dsimp only at hok
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok
  all_goals simp only [next, endOfTrip] at hn
  clc_sweep hn
  all_goals simp_all [D.clcFenced]

end Loader

namespace Mma

set_option maxHeartbeats 4000000 in
/-- The MMA thread polls the response barrier only at its CLC poll, with its phase, and arrives
only at its acknowledgement. -/
theorem clc_sites (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc →
      d.site = .clcWait ∧ p % 2 = d.cp % 2) ∧
    (∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc → d.site = .ack) := by
  refine ⟨fun p ok acq sc hk => ?_, fun tx c rel sc hk => ?_⟩
  · rcases wait_site hpre hi hat hc hf hk with ⟨s, -, h, -⟩ | ⟨-, h, -⟩ | ⟨hs, -⟩
    · have := s.isLt
      have := congrArg Loc.addr h
      simp only [clcResp, Bar.loc, Bar.off] at this
      omega
    · have := congrArg Loc.addr h
      simp only [clcResp, accBar, Bar.loc, Bar.off] at this
      omega
    · obtain ⟨p', _, _, _, hp', he⟩ := clcWait_event hpre hs hat hc hf
      rw [he] at hk
      simp only [Kind.wait.injEq] at hk
      exact ⟨hs, hk.2.1 ▸ hp'⟩
  · by_contra hs
    refine fires_notArrive (eventTmpl_notArrive (arriveOp_ne ?_)) hf _ _ _ _ _ hk
    obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
    cases site
    case ack => exact absurd rfl hs
    case full s => rw [code_full_ops s] at hc; cases hc; rfl
    case mma s j =>
      obtain ⟨ad, bd, en, hc'⟩ := code_mma s j
      rw [hc'] at hc
      cases hc
      rfl
    case commit s => rw [code_commit_ops s] at hc; cases hc; rfl
    all_goals (code_at hc; subst hc; rfl)

set_option maxHeartbeats 4000000 in
/-- The acknowledgement of an MMA thread arrives on the acknowledgement barrier of its cluster's
leader CTA. -/
theorem ack_arrive {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .ack) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ tx c rel sc, e = ⟨d.site.pc, .arrive (clcAck L g) tx c rel sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11)
  have hv : t.regs 855 = some (.ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
      (BitVec.ofNat 64 (L.sharedBase + 128))) :=
    (holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by mma_values))
  have hm := mbarClusterLoc_ptr hv hg (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
    (show readBits L g t 32 (.imm 0) = .ok (truncBits 32 (BitVec.ofInt 64 0)) by
      simp [readBits, pure, Except.pure])
    (show readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) by
      simp [readBits, pure, Except.pure]) hf
  have hl : (⟨.shared, 2 * (g / L.block / 2), L.sharedBase + 128⟩ : Loc) = clcAck L g := by
    simp [clcAck, Bar.loc, Bar.off]
  exact ⟨(truncBits 32 (BitVec.ofInt 64 0)).toNat, (truncBits 32 (BitVec.ofInt 64 1)).toNat,
    rel, sc, by rw [he, hl]⟩

set_option maxHeartbeats 8000000 in
theorem clc_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    GateStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView ∧
      LowStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView := by
  obtain ⟨hW, hA⟩ := clc_sites hpre hi hat hc hf
  obtain ⟨hok, har⟩ := clc_off hW hA
  have hack : d.site = .ack → arrivesOn (clcAck L g) e = true := by
    intro hs
    obtain ⟨tx, c, rel, sc, rfl⟩ := ack_arrive hpre hg hs hat hc hf
    simp [clcAck, Bar.loc, Bar.off, arrivesOn, sourceArrive]
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  have hcp : cp < 2 := hi.cp
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl hat hc hf
    obtain ⟨h1, h2⟩ := okPoll_clc (L := L) (g := g) (pc := Site.clcWait.pc) (p := p) (ok := ok)
      (acq := acq) (sc := sc)
    simp only [next, Option.some.injEq] at hn
    subst hn
    cases ok <;> simp [GateStep, LowStep, D.clcView, h1, h2, Site.done]
  all_goals clear hat hc hf hW hA
  all_goals dsimp only at hok har hack
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok har hack
  all_goals simp only [next, endOfTrip] at hn
  clc_sweep hn
  all_goals (simp only [GateStep, LowStep, D.clcView, hok]; try simp only [har])
  all_goals (split_ifs <;> first | (simp_all [Site.done]; done) | (simp_all [Site.done]; omega))

set_option maxHeartbeats 8000000 in
/-- A step into a fenced state is the proxy fence or keeps a fenced state, without a successful
response poll. -/
theorem fence_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next L g d e = some (some d')) :
    d'.clcFenced = true → okPoll (clcResp L g) e = false ∧
      (isFence e = true ∨ d.clcFenced = true) := by
  intro hfen
  obtain ⟨hW, hA⟩ := clc_sites hpre hi hat hc hf
  obtain ⟨hok, -⟩ := clc_off hW hA
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  cases site
  case clcFence =>
    code_at hc
    subst hc
    exact ⟨hok (by simp), .inl (fence_fires hf)⟩
  all_goals clear hat hc hf hW hA
  all_goals dsimp only at hok
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok
  all_goals simp only [next, endOfTrip] at hn
  clc_sweep hn
  all_goals simp_all [D.clcFenced]

end Mma

namespace Scheduler

set_option maxHeartbeats 4000000 in
/-- The scheduler polls the response barrier only at its CLC poll, with its phase, and arrives on
the acknowledgement barrier only at its acknowledgement. -/
theorem clc_sites (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc →
      d.site = .clcWait ∧ p % 2 = d.cp % 2) ∧
    (∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc → d.site = .ack) := by
  refine ⟨fun p ok acq sc hk => ?_, fun tx c rel sc hk => ?_⟩
  · rcases wait_site hpre hi hat hc hf hk with ⟨-, h, -⟩ | ⟨hs, -, rfl⟩
    · have := congrArg Loc.addr h
      simp only [clcResp, ackBar, Bar.loc, Bar.off] at this
      omega
    · exact ⟨hs, rfl⟩
  · rcases arrive_site hpre hg hat hc hf hk with ⟨-, h⟩ | ⟨hs, -⟩
    · have := congrArg Loc.addr h
      simp only [clcAck, respBar, Bar.loc, Bar.off] at this
      omega
    · exact hs

set_option maxHeartbeats 8000000 in
theorem clc_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    GateStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView ∧
      LowStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView := by
  obtain ⟨hW, hA⟩ := clc_sites hpre hg hi hat hc hf
  obtain ⟨hok, har⟩ := clc_off hW hA
  have hack : d.site = .ack → arrivesOn (clcAck L g) e = true := by
    intro hs
    obtain ⟨tx, c, rel, sc, rfl⟩ := ack_event hpre hg hs hat hc hf
    simp [clcAck, leadAck, Bar.loc, Bar.off, arrivesOn, sourceArrive]
  obtain ⟨site, ap, cp, r, x⟩ := d
  have hcp : cp < 2 := hi.cp
  cases site
  case clcWait =>
    obtain ⟨ok, acq, sc, he⟩ := clcWait_event hpre hi rfl hat hc hf
    subst he
    have h1 : okPoll (clcResp L g) ⟨Site.clcWait.pc, .wait (respBar L g) cp ok acq sc⟩ = ok := by
      rw [okPoll_wait rfl]
      simp
    simp only [next] at hn
    cases ok <;> simp only [Option.some.injEq, ↓reduceIte, Bool.false_eq_true] at hn <;>
      subst hn <;> simp [GateStep, LowStep, D.clcView, h1, arrivesOn, sourceArrive]
    omega
  all_goals clear hat hc hf hW hA
  all_goals dsimp only at hok har hack
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok har hack
  all_goals simp only [next, loopHead] at hn
  clc_sweep hn
  all_goals (simp only [GateStep, LowStep, D.clcView, hok]; try simp only [har])
  all_goals (split_ifs <;> simp_all)

set_option maxHeartbeats 8000000 in
/-- A step into a fenced state is the proxy fence or keeps a fenced state, without a successful
response poll. -/
theorem fence_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next L g d e = some (some d')) :
    d'.clcFenced = true → okPoll (clcResp L g) e = false ∧
      (isFence e = true ∨ d.clcFenced = true) := by
  intro hfen
  obtain ⟨hW, hA⟩ := clc_sites hpre hg hi hat hc hf
  obtain ⟨hok, -⟩ := clc_off hW hA
  obtain ⟨site, ap, cp, r, x⟩ := d
  cases site
  case clcFence =>
    code_at hc
    subst hc
    exact ⟨hok (by simp), .inl (fence_fires hf)⟩
  all_goals clear hat hc hf hW hA
  all_goals dsimp only at hok
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok
  all_goals simp only [next, loopHead] at hn
  clc_sweep hn
  all_goals simp_all [D.clcFenced]

end Scheduler

namespace Consumer

set_option maxHeartbeats 4000000 in
/-- The consumer thread polls the response barrier only at its CLC poll, with its phase, and
arrives on the acknowledgement barrier only at its acknowledgement. -/
theorem clc_sites (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc →
      d.site = .clcWait ∧ p % 2 = d.cp % 2) ∧
    (∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc → d.site = .ack) := by
  have : tidOf L g / 32 / 4 < 3 := by
    have := hpre.block
    have := Nat.mod_lt g (show 0 < L.block by omega)
    unfold tidOf
    omega
  refine ⟨fun p ok acq sc hk => ?_, fun tx c rel sc hk => ?_⟩
  · rcases wait_site hpre hi h hc hf hk with ⟨-, hm, -⟩ | ⟨hs, -, hp⟩
    · have := congrArg Loc.addr hm
      simp only [clcResp, accFull, accIdx, Bar.loc, Bar.off] at this
      omega
    · exact ⟨hs, hp⟩
  · rcases arrive_site hpre hg h hc hf hk with ⟨-, hm⟩ | ⟨hs, -⟩
    · have := congrArg Loc.addr hm
      simp only [clcAck, accEmpty, accIdx, Bar.loc, Bar.off] at this
      omega
    · exact hs

set_option maxHeartbeats 4000000 in
/-- The acknowledgement of a consumer thread arrives on the acknowledgement barrier of its
cluster's leader CTA: its arrival register holds that barrier. -/
theorem ack_arrive {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .ack) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ tx c rel sc, e = ⟨d.site.pc, .arrive (clcAck L g) tx c rel sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_12)
  have hv : t.regs 149 = some (.ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
      (BitVec.ofNat 64 (L.sharedBase + 128))) :=
    (holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))
  have hm := mbarClusterLoc_ptr hv hg (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
    (show readBits L g t 32 (.imm 0) = .ok (truncBits 32 (BitVec.ofInt 64 0)) by
      simp [readBits, pure, Except.pure])
    (show readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) by
      simp [readBits, pure, Except.pure]) hf
  have hl : (⟨.shared, 2 * (g / L.block / 2), L.sharedBase + 128⟩ : Loc) = clcAck L g := by
    simp [clcAck, Bar.loc, Bar.off]
  exact ⟨(truncBits 32 (BitVec.ofInt 64 0)).toNat, (truncBits 32 (BitVec.ofInt 64 1)).toNat,
    rel, sc, by rw [he, hl]⟩

set_option maxHeartbeats 8000000 in
theorem clc_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    GateStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView ∧
      (first L g = true → LowStep (clcResp L g) (arrivesOn (clcAck L g)) d.clcView e d'.clcView) :=
        by
  obtain ⟨hW, hA⟩ := clc_sites hpre hg hi h hc hf
  obtain ⟨hok, har⟩ := clc_off hW hA
  have hack : d.site = .ack → arrivesOn (clcAck L g) e = true := by
    intro hs
    obtain ⟨tx, c, rel, sc, rfl⟩ := ack_arrive hpre hg hs h hc hf
    simp [clcAck, Bar.loc, Bar.off, arrivesOn, sourceArrive]
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  have hcp : cp < 2 := hi.cp
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl h hc hf
    obtain ⟨h1, h2⟩ := okPoll_clc (L := L) (g := g) (pc := Site.clcWait.pc) (p := p) (ok := ok)
      (acq := acq) (sc := sc)
    simp only [next, Option.some.injEq] at hn
    subst hn
    cases ok <;> simp [GateStep, LowStep, D.clcView, h1, h2, Site.looping]
  all_goals clear h hc hf hW hA
  all_goals dsimp only at hok har hack
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok har hack
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals (simp only [GateStep, LowStep, D.clcView, hok]; try simp only [har])
  all_goals (split_ifs <;>
    first | (simp_all [Site.looping]; done) | (simp_all [Site.looping]; omega))

set_option maxHeartbeats 8000000 in
/-- A step into a fenced state is the proxy fence or keeps a fenced state, without a successful
response poll. -/
theorem fence_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next L g d e = some (some d')) :
    d'.clcFenced = true → okPoll (clcResp L g) e = false ∧
      (isFence e = true ∨ d.clcFenced = true) := by
  intro hfen
  obtain ⟨hW, hA⟩ := clc_sites hpre hg hi h hc hf
  obtain ⟨hok, -⟩ := clc_off hW hA
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case clcFence =>
    code_at hc
    subst hc
    exact ⟨hok (by simp), .inl (fence_fires hf)⟩
  all_goals clear h hc hf hW hA
  all_goals dsimp only at hok
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals simp_all [D.clcFenced]

end Consumer

/-- A role's first state holds nothing and expects the parity of no polls. -/
theorem Prologue.clc_start {p : Prologue.D} {e : Event} {r : Prologue.Role}
    (hn : Prologue.next L g p e = some (some (.inr r))) :
    r.clcView.pend = 0 ∧ r.clcView.ahead = 0 ∧ (r.clcView.live = true → r.clcView.par % 2 = 0) ∧
      r.clcFenced = false := by
  cases r with
  | loader l => rcases Prologue.next_loader hn with rfl | rfl <;>
      simp [Prologue.Role.clcView, Loader.D.clcView, Prologue.Role.clcFenced, Loader.D.clcFenced,
        Prologue.loaderStart, Prologue.loaderIdle]
  | mma m => rcases Prologue.next_mma hn with h | h <;>
      simp [Prologue.Role.clcView, Mma.D.clcView, Prologue.Role.clcFenced, Mma.D.clcFenced, h,
        Mma.Site.done]
  | sched s => rw [Prologue.next_sched hn]; simp [Prologue.Role.clcView, Scheduler.D.clcView,
      Prologue.Role.clcFenced, Scheduler.D.clcFenced, Prologue.schedStart]
  | cons c => rw [Prologue.next_cons hn]; simp [Prologue.Role.clcView, Consumer.D.clcView,
      Prologue.Role.clcFenced, Consumer.D.clcFenced, Prologue.consStart]

theorem mark_step {pre : List Event} {e : Event} {f f' : Bool}
    (h : MarkRel (clcResp L g) isFence f pre)
    (hs : f' = true → okPoll (clcResp L g) e = false ∧ (isFence e = true ∨ f = true)) :
    MarkRel (clcResp L g) isFence f' (pre ++ [e]) := by
  intro hf
  obtain ⟨hok, h'⟩ := hs hf
  exact MarkRel.step h hok (fun _ => h') hf

/-- Along a thread's run its CLC counts satisfy `ClcInv`. -/
theorem clcInv (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      ClcInv L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (ClcInv L g) quiet_nil ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · have hq' := hq.snoc (Prologue.fires_quiet hc hf)
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | r'
    · exact hq'
    · obtain ⟨h0, -, hpar, hfen⟩ := Prologue.clc_start hn
      exact ⟨GateRel.start ((hq' (clcAck L g)).2.1) ((hq' (clcResp L g)).1) h0 hpar,
        (fun h => by rw [hfen] at h; cases h), fun _ => LowRel.start (hq' (clcResp L g)).1⟩
  · obtain ⟨l', hl, rfl⟩ := next_of_loader hn
    obtain ⟨h1, h2⟩ := Loader.clc_step hpre hg hinv.1 hat hc hf hl
    exact ⟨hq.1.step h1, mark_step hq.2.1 (Loader.fence_step hpre hg hat hc hf hl),
      fun _ => (hq.2.2 rfl).step h2⟩
  · obtain ⟨m', hm, rfl⟩ := next_of_mma hn
    obtain ⟨h1, h2⟩ := Mma.clc_step hpre hg hinv.1 hat hc hf hm
    exact ⟨hq.1.step h1, mark_step hq.2.1 (Mma.fence_step hpre hinv.1 hat hc hf hm),
      fun _ => (hq.2.2 rfl).step h2⟩
  · obtain ⟨s', hs, rfl⟩ := next_of_sched hn
    obtain ⟨h1, h2⟩ := Scheduler.clc_step hpre hg hinv.1 hat hc hf hs
    exact ⟨hq.1.step h1, mark_step hq.2.1 (Scheduler.fence_step hpre hg hinv.1 hat hc hf hs),
      fun _ => (hq.2.2 rfl).step h2⟩
  · obtain ⟨c', hc', rfl⟩ := next_of_cons hn
    obtain ⟨h1, h2⟩ := Consumer.clc_step hpre hg hinv.1 hat.2.2.2.2 hc hf hc'
    exact ⟨hq.1.step h1,
      mark_step hq.2.1 (Consumer.fence_step hpre hg hinv.1 hat.2.2.2.2 hc hf hc'),
      fun hfst => (hq.2.2 hfst).step (h2 hfst)⟩

/-- A role's poll of its CTA's response barrier, and its acknowledgement, are at its CLC poll and
its acknowledgement: its view then expects the poll's parity, or holds one response. -/
theorem clc_role_sites (hpre : Pre P L mem0) (hg : g < L.threads) {r : Prologue.Role}
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inr r) t) (hinv : (code L g).inv (.inr r))
    (hc : kernel.code[(code L g).pc (.inr r)]? = some ins)
    (hf : Fires ((code L g).pc (.inr r)) (eventTmpl Prod L g t ins.op) e o) :
    (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc →
      r.clcView.live = true ∧ p % 2 = r.clcView.par % 2) ∧
    (∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc →
      r.clcView.pend = 1 ∧ r.clcView.ahead = 0 ∧ r.clcFenced = true) := by
  have key : ∀ {S : Type} {site poll ack : S} {cp : Nat} {v : GateView} {fen : Bool},
      (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc → site = poll ∧ p % 2 = cp % 2) →
      (∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc → site = ack) →
      (site = poll → v.live = true ∧ v.par % 2 = cp % 2) →
      (site = ack → v.pend = 1 ∧ v.ahead = 0 ∧ fen = true) →
      (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc → v.live = true ∧ p % 2 = v.par %
        2) ∧
      (∀ tx c rel sc, e.kind = .arrive (clcAck L g) tx c rel sc →
        v.pend = 1 ∧ v.ahead = 0 ∧ fen = true) :=
    fun hW hA hP hK => ⟨fun p ok acq sc hk => by
      obtain ⟨hs, hp⟩ := hW p ok acq sc hk
      obtain ⟨hl, hv⟩ := hP hs
      exact ⟨hl, by omega⟩, fun tx c rel sc hk => hK (hA tx c rel sc hk)⟩
  rcases r with ⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ | ⟨site, ap, cp, r, x⟩ |
    ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩
  · obtain ⟨hW, hA⟩ := Loader.clc_sites hpre hg hat hc hf
    exact key hW hA (fun h => by subst h; simp [Prologue.Role.clcView, Loader.D.clcView])
      (fun h => by subst h; simp [Prologue.Role.clcView, Loader.D.clcView, Prologue.Role.clcFenced,
        Loader.D.clcFenced])
  · obtain ⟨hW, hA⟩ := Mma.clc_sites hpre hinv.1 hat hc hf
    exact key hW hA (fun h => by subst h; simp [Prologue.Role.clcView, Mma.D.clcView,
      Mma.Site.done])
      (fun h => by subst h; simp [Prologue.Role.clcView, Mma.D.clcView, Prologue.Role.clcFenced,
        Mma.D.clcFenced])
  · obtain ⟨hW, hA⟩ := Scheduler.clc_sites hpre hg hinv.1 hat hc hf
    exact key hW hA (fun h => by subst h; simp [Prologue.Role.clcView, Scheduler.D.clcView])
      (fun h => by subst h; simp [Prologue.Role.clcView, Scheduler.D.clcView,
        Prologue.Role.clcFenced,
        Scheduler.D.clcFenced])
  · obtain ⟨hW, hA⟩ := Consumer.clc_sites hpre hg hinv.1 hat.2.2.2.2 hc hf
    exact key hW hA
      (fun h => by subst h; simp [Prologue.Role.clcView, Consumer.D.clcView, Consumer.Site.looping])
      (fun h => by subst h; simp [Prologue.Role.clcView, Consumer.D.clcView,
        Prologue.Role.clcFenced,
        Consumer.D.clcFenced])

/-- A role thread polls its CTA's response barrier with the parity of its successful polls,
and acknowledges after more successful polls than its earlier acknowledgements. -/
theorem clc_counts {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {r : Prologue.Role}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
    some (some (.inr r))) :
    (∀ p ok acq sc, e.kind = .wait (clcResp L g) p ok acq sc →
      p % 2 = okPolls (clcResp L g) ((X.tr g).take k) % 2) ∧
    (∀ tx n rel sc, e.kind = .arrive (clcAck L g) tx n rel sc →
      arrivals (clcAck L g) ((X.tr g).take k) + 1 ≤ okPolls (clcResp L g) ((X.tr g).take k) ∧
      ∃ j f, j < k ∧ X.get (g, j) = some f ∧ isFence f = true ∧
        okPolls (clcResp L g) ((X.tr g).take j) = okPolls (clcResp L g) ((X.tr g).take k)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨hW, hA⟩ := clc_role_sites hpre hg hat hinv hc hfire
  obtain ⟨h, hm, -⟩ := clcInv hpre hg htr k _ hσ
  refine ⟨fun p ok acq sc hk => GateRel.parity h (hW _ _ _ _ hk).1 (hW _ _ _ _ hk).2,
    fun tx n rel sc hk => ⟨GateRel.budget h (hA _ _ _ _ hk).1 (hA _ _ _ _ hk).2.1, ?_⟩⟩
  obtain ⟨j, f, hj, hfj, hfe, hcount⟩ := hm (hA _ _ _ _ hk).2.2
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  simp only [List.length_take, Nat.min_eq_left hk'] at hj
  refine ⟨j, f, hj, ?_, hfe, ?_⟩
  · rw [List.getElem?_take_of_lt hj] at hfj
    exact hfj
  · rw [List.take_take, Nat.min_eq_left hj.le] at hcount
    exact hcount

/-- A consumer thread selected by a consumer selector of its cluster is its group's first thread. -/
theorem first_of_selected (hpre : Pre P L mem0) {c g : Nat} {b : Fin 10}
    (hw : g % L.block / 32 < 8) (hb : ClcRing.consumerSel L c b g = true) :
    Consumer.first L g = true := by
  have hblock := hpre.block
  simp only [ClcRing.consumerSel, decide_eq_true_eq] at hb
  obtain ⟨-, hwarp, hlane⟩ := hb
  have hxy : g % L.block / 32 % 4 = 0 ∧ g % L.block % 32 = 0 := by
    rw [hblock] at hwarp hw ⊢
    fin_cases b <;> simp [ClcRing.warpOf, ClcRing.laneZero] at hwarp hlane hw <;>
      omega
  simp only [Consumer.first, Consumer.tidOf, decide_eq_true_eq]
  rw [hxy.1, hxy.2]
  rfl

/-- **The acknowledgements of a selected thread.** Its successful response polls are its
acknowledgement arrivals plus the response it holds: the gate relation and its converse. -/
theorem ack_exact_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {k : Nat} {d : ThreadD} (hg : g < L.threads)
    (hsel : ∃ b : Fin 10, ClcRing.consumerSel L (g / L.block / 2) b g = true)
    (hk : k ≤ (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    okPolls (clcResp L g) ((X.tr g).take k) =
      arrivals (clcAck L g) ((X.tr g).take k) + d.clcHeld := by
  have h := clcInv hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k d hσ
  rcases d with p | r
  · have hq : Quiet ((X.tr g).take k) := h
    rw [show ThreadD.clcHeld (.inl p) = 0 from rfl, (hq (clcResp L g)).1, (hq (clcAck L g)).2.1]
  · have hacks : r.acks L g = true := by
      rcases r with l | m | sd | cs
      iterate 3 rfl
      obtain ⟨b, hb⟩ := hsel
      exact first_of_selected hpre (role_warp hpre hX hg k hk (.cons cs) hσ) hb
    have hh : ThreadD.clcHeld (.inr r) = r.clcView.pend ∧ r.clcView.ahead = 0 := by
      rcases r with ⟨site⟩ | ⟨site⟩ | ⟨site⟩ | ⟨site⟩ <;> cases site <;> exact ⟨rfl, rfl⟩
    have hu := h.1.1
    have hl := h.2.2 hacks
    unfold LowRel at hl
    unfold arrivals
    omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
