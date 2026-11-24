-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderRetry
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaEvents
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCommits
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerExit
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # Progress facts of the threads

A loader at a slot's empty wait can poll that barrier with either outcome, and a failed poll
leaves it at the same wait (`loader_poll`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
/-- A loader at a slot's empty wait after its whole trace can poll that slot's empty barrier,
succeeding or failing; after a failed poll it is still at that wait. -/
theorem loader_poll {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {l : Loader.D} {b : Fin 8} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .wait b) (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(Loader.Site.wait b).pc,
        .wait (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) (InputRing.producerParity b)
          ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨(Loader.Site.wait b).pc, .wait (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))
          (InputRing.producerParity b) false true sc⟩]) = some (some (.inr (.loader l)))) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hat := hgood.1
  have hinv := hgood.2
  have hpc : (code L g).pc (.inr (.loader l)) = (Loader.Site.wait b).pc := by
    show l.site.pc = _
    rw [hs]
  have hout := Code.site_out (sound hpre hg) hgood
  have hc : kernel.code[l.site.pc]? = some ⟨none, .mbarWait (Loader.waitPred b)
      (Loader.waitBase b) 0 (.reg (Loader.waitPar b)) true .cta⟩ := by
    rw [hs]; exact Loader.code_wait_ops b
  rw [Code.tmpl, hpc, Loader.code_wait_ops b] at hout
  dsimp only at hout
  have htpc : t1.pc = l.site.pc := hat.1
  rcases mbarWait_tmpl (A := Prod) (L := L) (g := g) (t := t1) (p' := Loader.waitPred b)
      (b := Loader.waitBase b) (off := 0) (par := .reg (Loader.waitPar b)) (acq := true)
      (sc := .cta) with ⟨f, hw⟩ | ⟨m0, q, k, acq', sc', hw⟩
  · exfalso
    have hf : Fires l.site.pc (eventTmpl Prod L g t1 (.mbarWait (Loader.waitPred b)
        (Loader.waitBase b) 0 (.reg (Loader.waitPar b)) true .cta)) ⟨l.site.pc, .ub f⟩ none := by
      rw [hw]; exact ⟨rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Loader.wait_event hpre b hs hat hc hf
    cases he
  · have hf : Fires l.site.pc (eventTmpl Prod L g t1 (.mbarWait (Loader.waitPred b)
        (Loader.waitBase b) 0 (.reg (Loader.waitPar b)) true .cta))
        ⟨l.site.pc, .wait m0 q ok acq' sc'⟩ (some (k ok)) := by
      rw [hw]; exact ⟨ok, rfl, rfl⟩
    obtain ⟨ok', acq0, sc0, he⟩ := Loader.wait_event hpre b hs hat hc hf
    simp only [Event.mk.injEq, Kind.wait.injEq] at he
    obtain ⟨-, rfl, rfl, -, -, -⟩ := he
    obtain ⟨p1, b1, o1, q1, s1, hop, -⟩ := fires_wait_flags hf rfl
    simp only [Op.mbarWait.injEq] at hop
    obtain ⟨-, -, -, -, rfl, -⟩ := hop
    refine ⟨t1, k ok, sc', hl, ⟨.wait (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))
      (InputRing.producerParity b) k true sc', hout.trans (by rw [hw]), ?_⟩, ?_⟩
    · rw [htpc, hs]
      exact ⟨ok, rfl, rfl⟩
    · intro hok
      subst hok
      have hn : Loader.next L g l ⟨(Loader.Site.wait b).pc, .wait
          (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))
          (InputRing.producerParity b) false true sc'⟩ = some (some l) := by
        obtain ⟨site, m, n, q, cp, r, x⟩ := l
        simp only at hs
        subst hs
        simp [Loader.next]
      rw [Machine.after_snoc (code L g).toMachine (some (code L g).init) (X.tr g), hσ]
      simp [Code.toMachine, code, hn]

/-- The kernel's Tensor Core commits are at the commit pcs (decided on the code). -/
theorem kernel_tcCommit_pcs : OpPcs kernel.code commitOp Flow.tcCommit.toList = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- A Tensor Core commit is fired at an MMA thread's commit site or accumulator commit site. -/
theorem commit_role {L : Launch} {g : Nat} {d : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState}
    (hat : (code L g).AtD d t) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hfire : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) {sp : TcCommit.Spec}
    (hk : e.kind = .tc (.commit sp)) :
    ∃ m : Mma.D, d = .inr (.mma m) ∧ ((∃ s0, m.site = .commit s0) ∨ m.site = .accCommit) := by
  have hcm : commitOp ins.op = true := by
    cases h : commitOp ins.op
    · exact absurd hk (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) hfire sp)
    · rfl
  have hp : (code L g).pc d ∈ Flow.tcCommit.toList := OpPcs.mem kernel_tcCommit_pcs hc hcm
  rcases d with p | (l | m | sd | cs)
  · exact absurd hk (Prologue.notCommit_fires p.site hc hfire sp)
  · exfalso
    obtain ⟨site, mm, n, q, cp, r, x⟩ := l
    change site.pc ∈ _ at hp
    cases site <;> (exfalso; clear * - hp; revert hp; simp only [Loader.Site.pc]; decide +revert)
  · obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
    by_cases hs : site.commits = false
    · exact absurd hk (Mma.notCommit_fires site hs hc hfire sp)
    · have hs' : site.commits = true := by simpa using hs
      cases site with
      | commit s0 => exact ⟨⟨.commit s0, w, q, fp, ap, cp, r, x⟩, rfl, Or.inl ⟨s0, rfl⟩⟩
      | accCommit => exact ⟨⟨.accCommit, w, q, fp, ap, cp, r, x⟩, rfl, Or.inr rfl⟩
      | _ => simp [Mma.Site.commits] at hs'
  · exfalso
    obtain ⟨site, ap, cp, r, x⟩ := sd
    change site.pc ∈ _ at hp
    cases site <;> (exfalso; clear * - hp; revert hp; simp only [Scheduler.Site.pc]; decide +revert)
  · exfalso
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := cs
    change site.pc ∈ _ at hp
    cases site <;> (exfalso; clear * - hp; revert hp; simp only [Consumer.Site.pc]; decide +revert)

set_option maxHeartbeats 8000000 in
/-- A commit to slot `s`'s input empty barrier by an MMA thread of a leader CTA: its target at
rank `r < 2` is the same slot's barrier in the cluster's CTA `r`. -/
theorem commit_ranks_fact {P : Params} {L : Launch} {mem0 : Mem0} {g k : Nat} {X : Execution}
    {e : Event} {d : ThreadD} {sp : TcCommit.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) (s : Fin 4)
    (rank : Fin 16) (he : X.get (g, k) = some e)
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d))
    (hk : e.kind = .tc (.commit sp)) (hm : sp.mbar = inputEmpty L (g / L.block) s) (hr : rank.val <
      2) :
    TcCommit.target sp rank = some (inputEmpty L (g / L.block + rank.val) s) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨m, rfl, hsite⟩ := commit_role hat hc hfire hk
  rcases hsite with ⟨s0, hs0⟩ | hacc
  · obtain rfl := Mma.commit_event hpre hg s0 hs0 hat hc hfire
    have hsp : Mma.commitSpec L g s0 = sp := TcKind.commit.inj (Kind.tc.inj hk)
    subst hsp
    have hlead : Mma.Lead L g m := hinv.2.2
    have heven : g / L.block % 2 = 0 := by
      rcases hlead with h | h | h | h <;> first | exact h | simp [hs0] at h
    have hs0v : s0.val = s.val := by
      have h1 := congrArg Loc.addr hm
      simp [Mma.commitSpec, inputEmpty, Bar.loc, Bar.off] at h1
      omega
    obtain rfl : s0 = s := Fin.ext hs0v
    have hev2 : g / L.block / 2 * 2 = g / L.block := by omega
    have hcond : rank.val < (Mma.commitSpec L g s0).clusterSize ∧
        (Mma.commitSpec L g s0).mask.toNat / 2 ^ rank.val % 2 = 1 := by
      have : rank.val = 0 ∨ rank.val = 1 := by omega
      rcases this with h | h <;> simp [Mma.commitSpec, h]
    unfold TcCommit.target
    simp only [hcond.1, hcond.2, and_self, ↓reduceIte]
    simp [Mma.commitSpec, inputEmpty, Bar.loc, Bar.off, hev2, Nat.add_assoc]
  · exfalso
    obtain ⟨sp', hk', hmb⟩ := Mma.accCommit_event hpre hg hacc hat hc hfire
    subst hk'
    have hsp : sp' = sp := TcKind.commit.inj (Kind.tc.inj hk)
    subst hsp
    have h1 := congrArg Loc.addr (hmb.symm.trans hm)
    simp [inputEmpty, Bar.loc, Bar.off] at h1
    have := s.isLt
    omega

/-- An exit event fired at a role's exit site leads to no machine state. -/
theorem exit_role_next {L : Launch} {g : Nat} {d : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD d t) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hfire : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) (hk : e.kind = .exit) :
    (code L g).next d e = none := by
  have hp := ret_pc hc (fires_exit_op hfire hk)
  rcases d with p | (l | m | sd | cs)
  · exfalso
    obtain ⟨site, w⟩ := p
    change site.pc ∈ Flow.exit.toList at hp
    clear hc hfire hat hk
    revert hp
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
  · obtain ⟨site, mm, n, q, cp, r, x⟩ := l
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp;
                                    revert hp; simp only [Loader.Site.pc]; decide +revert)
    subst hsite
    simp [code, Loader.next]
  · obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp;
                                    revert hp; simp only [Mma.Site.pc]; decide +revert)
    subst hsite
    simp [code, Mma.next]
  · obtain ⟨site, ap, cp, r, x⟩ := sd
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp;
                                    revert hp; simp only [Scheduler.Site.pc]; decide +revert)
    subst hsite
    simp [code, Scheduler.next]
  · obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := cs
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp;
                                    revert hp; simp only [Consumer.Site.pc]; decide +revert)
    subst hsite
    simp [code, Consumer.next]

/-- A thread that exited has no machine state: its last event is an exit, which leads to none. -/
theorem exited_state_fact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    {pc : Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) (hl : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    Frame.stateAt (code L) X g (X.tr g).length = none := by
  obtain ⟨pre, hpe⟩ := List.getLast?_eq_some_iff.mp hl
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hta : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take pre.length) =
      (code L g).toMachine.after (some (code L g).init) pre := by
    rw [hpe, List.take_left' rfl]
  show (code L g).toMachine.after (some (code L g).init) ((X.tr g).take (X.tr g).length) = none
  rw [List.take_length, hpe, Machine.after_snoc (code L g).toMachine (some (code L g).init) pre
    ⟨pc, .exit⟩]
  cases ha : (code L g).toMachine.after (some (code L g).init) pre with
  | none => rfl
  | some τ =>
    rcases τ with _ | d'
    · exact absurd (hta.trans ha) (tracked hpre hX g pre.length hg)
    · have hj : (X.tr g)[pre.length]? = some ⟨pc, .exit⟩ := by rw [hpe]; simp
      have hta' : (code L g).toMachine.after (some (code L g).init)
          ((X.tr g).take pre.length) = some (some d') := hta.trans ha
      obtain ⟨o, hf⟩ := htr.fired_at hj hta'
      obtain ⟨t, ins, hat, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
      exact exit_role_next hat hc hfire rfl

end
end PTX.Kernels.Fp16Gemm8192.Proof
