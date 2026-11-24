-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.ClusterScopeMbar

@[expose] public section

/-!
# Assumption constructor `pollAgreeAt`

A kernel declares the poll-agreement assumption with `Assumption.pollAgreeAt`, naming exactly the
guarded `bra.uni` sites after a poll at which its proof exempts two lanes' executions whose polls
right before are of one mbarrier. This file is not itself an assumption.
-/

namespace PTX.Assumption

/-! ## ASM-POLL-AGREE — lanes of a warp spinning on one poll stay converged and agree
Statement: At the guarded `bra.uni` sites a kernel names that branch on the result of an
  `mbarrier.try_wait`, the model trusts that the lanes of a warp polling one mbarrier get the same
  result, and it does not compare their branches. A kernel that branches on the poll with a plain
  `bra`, or votes the result across the warp before the `bra.uni`, does not need this assumption.

Defs: Assumption.pollAgreeAt

Source:
- §9.7.14.3: "bra.uni is guaranteed to be non-divergent, i.e. all active threads in a warp that
    are currently executing this instruction have identical values for the guard predicate and
    branch target"
- §9.7.15.16.19: "Suspended thread resumes execution when the specified phase completes OR before
    the phase completes following a system-dependent time limit"
- §3.2: "A schedule optimizer determines how to group active threads from the same warp together
    into SIMT units"
- ERR-NONUNIFORM-GUARD

Direction: trust

Effect: `pollAgreeAt name sites why` selects, at exactly the sites (`pc`) in `sites`, the hook
  `uniPoll` (ASM-INTERFACE). Two executions there are not compared when the instruction at the site
  is a `bra.uni` guarded by the predicate that the `mbarrier.try_wait` right before it writes and
  both lanes' records right before are that poll's events on one mbarrier, whatever their
  parities. `PollAgreeExempt` checks the instruction form: a selected site that holds any other
  instruction, or a `bra.uni` that does not follow such a poll, is not exempted. Polls of
  different objects are still compared. If lanes can execute the branch together with different
  poll results, that is undefined behaviour that the theorem does not report. The constructor
  adds no constraint on executions and sets no `wf` and no `ub`. The statement is generated from
  the sites and lists every site it covers.

Review: `mbarrier.try_wait` is defined per executing thread and may return False before the phase
  completes, so two lanes of a warp that poll one mbarrier at one position can hold different poll
  results. ERR-NONUNIFORM-GUARD then compares their executions of the `bra.uni` that branches on the
  result, unless the execution-dependency order (EXT-DEPENDENCY-ORDER) orders them. Lanes that
  poll in one round are never so ordered, and lanes a round apart are not ordered when no blocking
  collective or synchronization lies between the rounds. CUTLASS- and CuTe-generated wait loops
  are `mbarrier.try_wait P; @P bra.uni DONE;`, which by §9.7.14.3 is undefined unless `P` is
  identical among the lanes executing the branch together (checked 2026-11-13 on CuTe DSL
  `dense_gemm_persistent.py`, CUTLASS e406c186, DSL 4.7.1, which also passes on B200). They rely
  on a hardware behaviour that the text does not state: lanes of a warp spinning on such a poll
  stay converged and get the same poll result. A program avoids the assumption by branching on the
  poll with a plain `bra` (DeepGEMM does), or by a warp vote of the result before a `bra.uni`.
-/

/-- At exactly the guarded `bra.uni` sites `sites` after a poll, two lanes' executions after polls
of one mbarrier are not compared, whatever the polls' parities; `why` says why the kernel needs
it. -/
def pollAgreeAt (name : String) (sites : List Nat) (why : String) : Assumption where
  name := name
  statement := s!"Lanes of one warp spinning in a wait loop on one mbarrier stay converged and get \
    the same poll result: a bra.uni guarded by the predicate of the mbarrier.try_wait right before \
    it is never executed together by two lanes whose poll results differ, also when they poll \
    different phases of the mbarrier, at exactly these sites: {siteText sites}. {why}"
  uniPoll pc := sites.contains pc

end PTX.Assumption
