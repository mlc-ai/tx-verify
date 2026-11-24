-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Lemmas.Flow.NotCommit
import Lemmas.Flow.CommitTarget
import Lemmas.Flow.NotBulk
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # MMA commit-object destinations -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingCommitEvents

open PTX PTX.Proof PTX.Flow

local macro "decide_site" : tactic =>
  `(tactic| first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

private def commits : List Nat := Flow.tcCommit.toList

set_option maxRecDepth 100000 in
private theorem commit_sites : OpPcsFast kernel.code commitOp commits = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem only_single_cta_commits :
    OpPcsFast kernel.code (fun op => match op with
      | .tcCommit .two .. => true
      | _ => false) [] = true := by
  decide +kernel

/-- Every issued Tensor Core commit resolves to an existing single-CTA group. -/
theorem no_commit_unsafe {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ TcCommitUnsafe L X := by
  rintro ⟨⟨g, i⟩, sp, ⟨site, he⟩, hbad⟩
  have hg := Frame.lt_of_get hX he
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  cases hop : commitOp ins.op
  · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne hop)) hf sp rfl).elim
  · cases hi : ins.op <;> simp only [hi, commitOp, Bool.false_eq_true] at hop
    rename_i group base off mask
    cases group
    case two =>
      have h := OpPcsFast.mem only_single_cta_commits hc (by rw [hi])
      exact List.not_mem_nil h
    case one =>
      rw [hi] at hf
      obtain ⟨m, bits, hr⟩ := tcCommit_resolves hf rfl
      have hsz (k : Nat) : L.clusterSizeAt k = 1 := by
        simp [Launch.clusterSizeAt, hpre.clusterPlaces, gridPlace, Dim3.prod]
      have hloc (n k c : Nat) : L.locate n k c = (k + c, 0) := by
        rw [Launch.locate_regular (fun k => by
          change L.clusterSizeAt k = L.clusterSize.val
          rw [hsz, hpre.clusterSize]), hpre.clusterSize, Nat.div_one, Nat.mod_one]
      have hstart (k : Nat) : L.clusterStart k = k := by
        induction k with
        | zero => rfl
        | succ k ih => rw [Launch.clusterStart, ih, hsz]
      unfold TcCommit.resolve at hr
      split at hr
      · rename_i hValid
        have hGrid : g / L.block < L.grid := hValid.2.1
        cases hr
        refine hbad ⟨hg, ?_, ?_⟩
        · simp [TcCommit.resolve, hValid]
        · simp [Launch.ctaGroup_one, Launch.peerCta, Launch.clusterOfCta, Launch.rankOfCta,
            Launch.clusterSizeOf, hloc, hstart, hsz, hGrid]
      · cases hr

variable {P : Params} {L : Launch}

private theorem commit_pc_of_fired {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {sp : TcCommit.Spec} (hf : (Machine.machine P L g).Fired (some d) e o)
    (hk : e.kind = .tc (.commit sp)) :
    (Machine.code P L g).pc d ∈ commits := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    obtain ⟨he, _⟩ := hf
    rw [he] at hk
    contradiction
  | some ins =>
    rw [hc] at hf
    cases hOp : commitOp ins.op
    · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne hOp)) hf sp hk).elim
    · exact OpPcsFast.mem commit_sites hc hOp

private theorem fired_at_code {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {ins : Instr} (hf : (Machine.machine P L g).Fired (some d) e o)
    (hc : kernel.code[(Machine.code P L g).pc d]? = some ins) :
    ∃ t, (Machine.code P L g).AtD d t ∧
      Fires ((Machine.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Machine.code P L g).AtD d t at hat
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hat.1, hc] at hf
  exact ⟨t, hat, hf⟩


def CommitSite : Machine.ThreadD → Prop
  | .mma q => q.site = .qCopyCommit ∨ q.site = .qkCommit ∨ q.site = .pvCommit
  | _ => False

theorem commit_site {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {sp : TcCommit.Spec} (hf : (Machine.machine P L g).Fired (some d) e o)
    (hk : e.kind = .tc (.commit sp)) :
    CommitSite d := by
  have hm := commit_pc_of_fired hf hk
  clear * - d hm
  cases d
  case prologue q =>
    change q.pc ∈ _ at hm
    change False
    cases q <;> revert hm <;> decide_site
  case wg0 q =>
    change q.site.pc ∈ _ at hm
    simp only [CommitSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case mma q =>
    change q.site.pc ∈ _ at hm
    simp only [CommitSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case tma q =>
    change q.site.pc ∈ _ at hm
    simp only [CommitSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case index q =>
    change q.site.pc ∈ _ at hm
    simp only [CommitSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case wg2 q =>
    change q.site.pc ∈ _ at hm
    simp only [CommitSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case idle q =>
    change q.pc ∈ _ at hm
    change False
    cases q <;> revert hm <;> decide
  case head =>
    change 1843 ∈ _ at hm
    exact (by decide : 1843 ∉ commits) hm
  case done =>
    change 3611 ∈ _ at hm
    exact (by decide : 3611 ∉ commits) hm


private theorem local_commit_template {mem0 : Mem0} {g base off : Nat} {t : TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hr : t.regs base = some (b32 (L.sharedBase + off)))
    (hb : L.sharedBase + off < 2 ^ 32) (ha : (L.sharedBase + off) % 8 = 0) :
    ∃ sp : TcCommit.Spec,
      eventTmpl Assumptions.all L g t (.tcCommit .one base 0 none) = .tc (.commit sp) (PTX.next t) ∧
      sp.mbar = ⟨.shared, ctaOf L g, L.sharedBase + off⟩ ∧
      ∀ rank, TcCommit.target sp rank = if rank = 0 then some sp.mbar else none := by
  let loc : Loc := ⟨.shared, g / L.block, L.sharedBase + off⟩
  have hm : mbarClusterLoc L g t base 0 = .ok loc := mbarClusterLoc_b32 hr hb ha
  have hsz (k : Nat) : L.clusterSizeAt k = 1 := by
    simp [Launch.clusterSizeAt, hpre.clusterPlaces, gridPlace, Dim3.prod]
  have hloc (n k c : Nat) : L.locate n k c = (k + c, 0) := by
    rw [Launch.locate_regular (fun k => by
      change L.clusterSizeAt k = L.clusterSize.val
      rw [hsz, hpre.clusterSize]), hpre.clusterSize, Nat.div_one, Nat.mod_one]
  have hcta (c : Nat) : L.clusterOfCta c = c := by
    simp [Launch.clusterOfCta, hloc]
  have hstart (k : Nat) : L.clusterStart k = k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Launch.clusterStart, ih, hsz]
  have hgrid : g / L.block < L.grid := by
    rw [Launch.threads, hpre.block] at hg
    rw [hpre.block]
    omega
  have hRank : L.rankOfCta loc.cta = 0 := by simp [Launch.rankOfCta, hloc]
  have hSize : L.clusterSizeOf (g / L.block) = 1 := hsz _
  let sp : TcCommit.Spec := ⟨.one, loc, BitVec.ofNat 16 1, loc.cta, 1⟩
  have hResolve :
      TcCommit.resolve L .one (g / L.block) loc (BitVec.ofNat 16 (2 ^ L.rankOfCta loc.cta)) =
        some sp := by
    simp [TcCommit.resolve, hpre.launchValid.1, hRank, hSize, hcta, hstart, hgrid, loc, sp]
  refine ⟨sp, ?_, rfl, fun rank => ?_⟩
  · simp only [eventTmpl, tcCommitTmpl, hg, ↓reduceIte, hm, bind, Except.bind, pure, Except.pure,
      hResolve, ofExec]
  · fin_cases rank <;> simp [TcCommit.target, sp, loc]

/-- The pending commit at any of the three MMA sites has its local barrier and rank zero. -/
theorem commit_template {g : Nat} {mem0 : Mem0} {d : Wg1Mma.D} {t : TState} {ins : Instr}
    (hpre : Pre P L mem0) (hg : g < L.threads)
    (hd : d.site = .qCopyCommit ∨ d.site = .qkCommit ∨ d.site = .pvCommit)
    (hat : (Wg1Mma.code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins) :
    let off := if d.site = .qCopyCommit then 222784
      else if d.site = .qkCommit then 222904 + 8 * (d.i % 2) else 222936 + 8 * (d.i % 2)
    ∃ sp : TcCommit.Spec,
      eventTmpl Assumptions.all L g t ins.op = .tc (.commit sp) (PTX.next t) ∧
      sp.mbar = ⟨.shared, ctaOf L g, L.sharedBase + off⟩ ∧
      ∀ rank, TcCommit.target sp rank = if rank = 0 then some sp.mbar else none := by
  rcases hd with hd | hd | hd
  · have hpc : d.site.pc = 1982 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_0)
    have hreg : t.regs 843 = some (b32 (L.sharedBase + 222784)) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some,
        Wg1Mma.qUtccpAddr_eq, Nat.add_assoc] using
        Wg1Mma.atD_reg hat (r := 843) hpc (by decide +kernel)
    have hb := sharedBase_lt hpre
    have ha := Wg2.sharedAddr_align hpre (by omega : 222784 % 8 = 0)
    simpa [hd] using local_commit_template hpre hg hreg (by omega) ha
  · have hpc : d.site.pc = 2105 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_1)
    have hreg : t.regs 877 = some (b32 (L.sharedBase + (222904 + 8 * (d.i % 2)))) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some,
        Wg1Mma.qkDoneAddr_eq, Nat.add_assoc] using
        Wg1Mma.atD_reg hat (r := 877) hpc (by decide +kernel)
    have hb := sharedBase_lt hpre
    have ha := Wg2.sharedAddr_align hpre (by omega : (222904 + 8 * (d.i % 2)) % 8 = 0)
    simpa [hd] using local_commit_template hpre hg hreg (by omega) ha
  · have hpc : d.site.pc = 2148 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_2)
    have hreg : t.regs 883 = some (b32 (L.sharedBase + (222936 + 8 * (d.i % 2)))) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some,
        Wg1Mma.svDoneAddr_eq, Nat.add_assoc] using
        Wg1Mma.atD_reg hat (r := 883) hpc (by decide +kernel)
    have hb := sharedBase_lt hpre
    have ha := Wg2.sharedAddr_align hpre (by omega : (222936 + 8 * (d.i % 2)) % 8 = 0)
    simpa [hd] using local_commit_template hpre hg hreg (by omega) ha

/-- The exact commit event fired at each Tensor Core commit site. -/
theorem commit_issue {g : Nat} {mem0 : Mem0} {d : Wg1Mma.D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads)
    (hd : d.site = .qCopyCommit ∨ d.site = .qkCommit ∨ d.site = .pvCommit)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o) :
    let off := if d.site = .qCopyCommit then 222784
      else if d.site = .qkCommit then 222904 + 8 * (d.i % 2) else 222936 + 8 * (d.i % 2)
    ∃ sp : TcCommit.Spec, e.kind = .tc (.commit sp) ∧
      sp.mbar = ⟨.shared, ctaOf L g, L.sharedBase + off⟩ ∧
      ∀ rank, TcCommit.target sp rank = if rank = 0 then some sp.mbar else none := by
  have hCode : ∃ ins, kernel.code[d.site.pc]? = some ins := by
    rcases hd with hs | hs | hs
    · rw [hs]; exact ⟨_, Flow.code_tcCommit_0⟩
    · rw [hs]; exact ⟨_, Flow.code_tcCommit_1⟩
    · rw [hs]; exact ⟨_, Flow.code_tcCommit_2⟩
  obtain ⟨ins, hc⟩ := hCode
  obtain ⟨t, hat, hF⟩ := fired_at_code hf hc
  obtain ⟨sp, hTmpl, hm, hRank⟩ := commit_template hpre hg hd hat hc
  rw [hTmpl] at hF
  exact ⟨sp, congrArg Event.kind hF.1, hm, hRank⟩

/-- The event of the PV commit is selected by the lifetime ordering assumption. -/
theorem pv_commit_order_selected {g : Nat} {d : Wg1Mma.D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o) (hd : d.site = .pvCommit) :
    Assumptions.all.any (·.commitInOrder e.pc) = true := by
  obtain ⟨t, hat, hfire⟩ := hf
  have hpc := fires_pc hfire
  have hAt : t.pc = d.site.pc := hat.1.1
  rw [Assumptions.all_commitInOrder, hpc, hAt, hd]
  decide +kernel

/-- An MMA notification records its issuing state and the local object named by the commit. -/
theorem commit_source {g : Nat} {mem0 : Mem0} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .tc (.commit sp))
    (ht : TcCommit.target sp rank = some m) :
    m = sp.mbar ∧ ∃ q : Wg1Mma.D, d = .mma q ∧
      ((q.site = .qCopyCommit ∧ m = ⟨.shared, ctaOf L g, L.sharedBase + 222784⟩) ∨
        (q.site = .qkCommit ∧ m = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (q.i % 2))⟩) ∨
        (q.site = .pvCommit ∧
          m = ⟨.shared, ctaOf L g, L.sharedBase + (222936 + 8 * (q.i % 2))⟩)) := by
  have hsite := commit_site hf hk
  cases d
  case mma q =>
    obtain ⟨sp', he', hm, htarget⟩ := commit_issue hpre hg hsite hf
    obtain rfl := TcKind.commit.inj (Kind.tc.inj (hk.symm.trans he'))
    rw [htarget] at ht
    split at ht
    · have hl := Option.some.inj ht
      refine ⟨hl.symm, q, rfl, ?_⟩
      rcases hsite with hs | hs | hs
      · exact .inl ⟨hs, by simpa [hs] using hl.symm.trans hm⟩
      · exact .inr (.inl ⟨hs, by simpa [hs] using hl.symm.trans hm⟩)
      · exact .inr (.inr ⟨hs, by simpa [hs] using hl.symm.trans hm⟩)
    · cases ht
  all_goals exact hsite.elim

/-- Every MMA notification targets the fixed query-copy object or one GEMM completion object. -/
theorem commit_address {g : Nat} {mem0 : Mem0} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .tc (.commit sp))
    (ht : TcCommit.target sp rank = some m) :
    m.addr = L.sharedBase + 222784 ∨
      (∃ buf : Fin 2, m.addr = L.sharedBase + (222904 + 8 * buf.val)) ∨
      ∃ buf : Fin 2, m.addr = L.sharedBase + (222936 + 8 * buf.val) := by
  obtain ⟨_, q, _, ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, hm⟩⟩ := commit_source hpre hg hf hk ht
  · exact .inl (congrArg Loc.addr hm)
  · exact .inr (.inl ⟨⟨q.i % 2, by omega⟩, congrArg Loc.addr hm⟩)
  · exact .inr (.inr ⟨⟨q.i % 2, by omega⟩, congrArg Loc.addr hm⟩)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingCommitEvents
