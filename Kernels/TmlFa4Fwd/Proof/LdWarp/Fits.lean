-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Round
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Sim
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedWords
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' reference values

The loader's scheduler is the output warp's on its scan state, so its reference values are the
output warp's (`Epilogue.Fits`) on `toE d`, with the thread's shuffle count shifted by the shuffles
of the tile's packets so far: 32 per committed packet (`nc`, the ledger's commits) and the rows'
shuffles of the current packet (`pktSh`). In the blocks the tile's block word is the reference
one of the picked tile (`SuRef`) and the round counter and the commits follow `Rounds`; in the
second pass all the tile's packets are committed (`pkts`). So the second pass's positions are the
same on every lane of the CTA.

The classes of sites (`lc`): the `setmaxnreg`, the first pass, the request's reads, the blocks,
the second pass, the drain (whose output-warp site is the return of the pass it ends). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked qv)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The classes of loader sites. -/
inductive LC where
  | early | p1 | req | blk | p2 | drain
  deriving DecidableEq

/-- The class of a site. -/
def lc : Site → LC
  | .setmax => .early
  | .word k | .down k | .up k _ | .total k => if k.late then .p2 else .p1
  | .vote l | .pre l | .tiles l => if l then .p2 else .p1
  | .q0 | .q1 | .uk => .req
  | .dw _ | .dq | .de | .da | .exit => .drain
  | _ => .blk

theorem lc_blk {s : Site} : lc s = .blk ↔ s.blk = true := by
  cases s <;> simp [lc, Site.blk, bc] <;> split <;> simp

/-- The loader's values of the tile the first pass picked after its scan ended at round `R` with
ballot `bal`: the scan state, the request's offsets and used-K length, the coordinates. -/
def refVL (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : V :=
  let c := Epilogue.chosenD p (g / L.block) R bal
  let sc : Epilogue.D := { c with c0 := qv p (chosen c), c1 := qv p (addi (chosen c) 1) }
  { sc := sc, ukw := ukv p (chosen c), co := coords p L g sc }

/-- The block word of the picked tile. -/
def r28Ref (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : BitVec 64 :=
  (setup p L g (refVL p L g R bal)).r28

/-- The tile's block word is the picked tile's. -/
def SuRef (p : Params) (L : Launch) (g : Nat) (v : V) : Prop :=
  ∃ R bal, Picked p L g R bal ∧ v.su.r28 = r28Ref p L g R bal

/-- **The page-table facts at a block state**: the setup words are the setup of a state with the
same scan state and used-K word, the used-K word is the chosen request's, the later blocks' first
block (`%r56`) is the tile's blocks less two, and a page-table load's row is inside the used length
(`RowOk`). -/
def PgOk (p : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  (∃ v₀ : V, d.v.su = setup p L g v₀ ∧ v₀.ukw = d.v.ukw ∧ v₀.sc = d.v.sc) ∧
    d.v.ukw = ukv p (chosen d.v.sc) ∧
    (bc d.site ≠ some .prime → d.v.r56 = addi d.v.su.r28 (-2)) ∧ RowOk p L g d

/-- **The reference values at a state of a loader lane**, with the thread's shuffles `ns`,
full-mask ballots `nv` and commits `nc` before it. -/
def LFits (p : Params) (L : Launch) (g : Nat) (d : D) (ns nv nc : Nat) : Prop :=
  match lc d.site with
  | .early => ns = 3 ∧ nv = 0 ∧ nc = 0
  | .p1 => nc = 0 ∧ Epilogue.Fits p L g (toE d) ns nv
  | .req => nc = 0 ∧ Epilogue.Fits p L g (toE d) ns nv ∧ d.v.co = coords p L g d.v.sc
  | .blk => 32 * nc + pktSh d.site ≤ ns ∧
      Epilogue.Fits p L g (toE d) (ns - 32 * nc - pktSh d.site) nv ∧ SuRef p L g d.v ∧
      Rounds d.site d.v nc ∧ PgOk p L g d
  | .p2 => 32 * nc ≤ ns ∧ Epilogue.Fits p L g (toE d) (ns - 32 * nc) nv ∧ SuRef p L g d.v ∧
      nc = pkts d.v.su.r28
  | .drain => ∃ l, 32 * nc ≤ ns ∧
      Epilogue.Fits p L g { d.v.sc with site := .exit l } (ns - 32 * nc) nv ∧
      (l = true → SuRef p L g d.v ∧ nc = pkts d.v.su.r28) ∧ (l = false → nc = 0)

/-- What the reference says an event at a loader state returns: the output warp's reference at a
scheduler site (at the shifted count in the second pass), the launch's used-K length at its read. -/
def LExpect (p : Params) (L : Launch) (g : Nat) (d : D) (ns nc : Nat) (e : Event) : Prop :=
  match d.site, e.kind with
  | .uk, .rd _ bs => rebuild 3 bs = .ok (.bits 32 (ukv p (chosen d.v.sc)))
  | s, _ => (s.sched || s.scan) = true → Epilogue.Expect p L g (toE d) (ns - 32 * nc) e

variable {p : Params} {L : Launch} {g w : Nat}

/-- The pass of a loader site of the scheduler (`false` elsewhere). -/
def Site.lateL : Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l => l
  | _ => false

theorem epi_lateE {s : Site} (hs : s.sched = true) : Mma.lateE s.epi = s.lateL := by
  cases s <;> simp_all [Site.sched, Site.epi, Mma.lateE, Site.lateL]

/-- **A scheduler step reaches a scheduler site, a read, or the end**, in the same pass. -/
theorem succ_back {d : D} {e : Event} {c : Epilogue.D} (hs : d.site.sched = true)
    (h : Epilogue.succ p L g (toE d) e = some (some c)) :
    Mma.backE c.site = true ∧ Mma.lateE c.site = d.site.lateL ∧
      ((c.site = .q1 ∨ ∃ st, c.site = .ready st) → d.site = .q0 ∨ d.site = .q1) ∧
      c.site ≠ .q0 := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  all_goals cases kind <;> simp only [Epilogue.succ, Site.epi, reduceCtorEq] at h
  all_goals try simp only [Epilogue.word32, Epilogue.afterTotal, Epilogue.loopHead,
    Epilogue.scanExit] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq, Option.some.injEq] at h
  all_goals first
    | (subst h; simp_all [Mma.backE, Mma.lateE, Site.lateL, Epilogue.loopOf, Epilogue.Scan.late];
       done)
    | (cases h; done)
    | (simp_all; done)

/-- The class of the loader site of an output-warp site a scheduler step reaches. -/
theorem lc_ofE {s : Epilogue.Site} (hb : Mma.backE s = true) :
    lc (Site.ofE s) = (match s with
      | .exit _ => .drain
      | .q0 | .q1 | .ready _ => .req
      | _ => if Mma.lateE s then .p2 else .p1) := by
  cases s <;> first | (simp [Mma.backE] at hb; done) | rfl | (cases ‹Bool› <;> rfl)

theorem toE_ofE {d : D} {c : Epilogue.D} (hb : Mma.backE c.site = true)
    (hx : ∀ l, c.site ≠ .exit l) : toE (ofE d c) = c := by
  obtain ⟨s, rest⟩ := c
  cases s <;> simp_all [Mma.backE, toE, ofE, Site.ofE, Site.epi]

theorem ofE_sc (d : D) (c : Epilogue.D) : (ofE d c).v.sc = { c with site := d.v.sc.site } := by
  simp only [ofE, D.mk']

theorem ofE_su (d : D) (c : Epilogue.D) : (ofE d c).v.su = d.v.su := by
  simp only [ofE, D.mk']; unfold vOf; split <;> rfl

theorem ofE_co (d : D) (c : Epilogue.D) : (ofE d c).v.co = d.v.co := by
  simp only [ofE, D.mk']; unfold vOf; split <;> rfl

/-- The events of a scheduler site add no commit. -/
theorem cm_sched {d : D} {e : Event} (hs : d.site.sched = true) (hev : Ev p L g w d e) :
    cm e = 0 := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  all_goals simp only [Ev, Epilogue.Ev, Site.toE] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals rfl

/-- At a scheduler site: the class, the commits and the output warp's values at the shifted
count. -/
theorem sched_fits {d : D} {ns nv nc : Nat} (hs : d.site.sched = true)
    (hF : LFits p L g d ns nv nc) :
    32 * nc ≤ ns ∧ Epilogue.Fits p L g (toE d) (ns - 32 * nc) nv ∧
      (d.site.lateL = false → nc = 0 ∧ (lc d.site = .req → d.v.co = coords p L g d.v.sc)) ∧
      (d.site.lateL = true → SuRef p L g d.v ∧ nc = pkts d.v.su.r28) := by
  obtain ⟨s, v, kk⟩ := d
  have scan : ∀ l : Bool, (if l then LC.p2 else LC.p1) = lc s → s.lateL = l →
      32 * nc ≤ ns ∧ Epilogue.Fits p L g (toE ⟨s, v, kk⟩) (ns - 32 * nc) nv ∧
      (s.lateL = false → nc = 0 ∧ (lc s = .req → v.co = coords p L g v.sc)) ∧
      (s.lateL = true → SuRef p L g v ∧ nc = pkts v.su.r28) := by
    intro l hl hll
    simp only [LFits, ← hl] at hF
    cases l <;> simp only [Bool.false_eq_true, ↓reduceIte] at hF
    · obtain ⟨h0, h1⟩ := hF; subst h0
      exact ⟨by omega, by simpa using h1, fun _ => ⟨rfl, fun h => by rw [← hl] at h; cases h⟩,
        fun h => by rw [hll] at h; cases h⟩
    · obtain ⟨h0, h1, h2, h3⟩ := hF
      refine ⟨h0, h1, fun h => ?_, fun _ => ⟨h2, h3⟩⟩
      rw [hll] at h; cases h
  cases s with
  | word k | down k | total k => exact scan k.late rfl rfl
  | up k j => exact scan k.late rfl rfl
  | vote l | pre l => exact scan l rfl rfl
  | q0 | q1 =>
    simp only [LFits, lc] at hF
    obtain ⟨h0, h1, h2⟩ := hF; subst h0
    exact ⟨by omega, by simpa using h1, fun _ => ⟨rfl, fun _ => h2⟩, by simp [Site.lateL]⟩
  | _ => simp [Site.sched] at hs

theorem lexpect_sched {d : D} {ns nc : Nat} {e : Event} (hs : d.site.sched = true)
    (hE : LExpect p L g d ns nc e) : Epilogue.Expect p L g (toE d) (ns - 32 * nc) e := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, k⟩ := e
  cases s <;> simp only [LExpect] at hE <;>
    first | exact hE (by simp [hs]) | simp [Site.sched] at hs

/-- The output warp's step at a scheduler site keeps its reference values. -/
theorem efits_sched {d : D} {e : Event} {c : Epilogue.D} {n nv : Nat} (hs : d.site.sched = true)
    (hF : Epilogue.Fits p L g (toE d) n nv) (hE : Epilogue.Expect p L g (toE d) n e)
    (hev : Ev p L g w d e) (hc : Epilogue.succ p L g (toE d) e = some (some c)) :
    Epilogue.Fits p L g c (n + Epilogue.sh e) (nv + Epilogue.vt e) := by
  by_cases hsc : d.site.scan = true
  · have hev' : Epilogue.Ev p L g (toE d) e := by
      obtain ⟨s, v, kk⟩ := d
      cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;>
        simpa only [Ev, toE, Site.epi, Site.toE] using hev
    exact Epilogue.fits_next (ent := fun _ => .pred false) hF hE hev' hc
  · obtain ⟨s, v, kk⟩ := d
    have hq : s = .q0 ∨ s = .q1 := by cases s <;> simp_all [Site.sched, Site.scan]
    have hsh : Epilogue.sh e = 0 ∧ Epilogue.vt e = 0 := by
      obtain ⟨pc, k⟩ := e
      rcases hq with rfl | rfl <;> simp only [Ev] at hev <;>
        rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> exact ⟨rfl, rfl⟩
    rw [hsh.1, hsh.2, Nat.add_zero, Nat.add_zero]
    have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal (toE ⟨s, v, kk⟩) n nv := by
      rcases hq with rfl | rfl <;> simp only [Epilogue.Fits, toE, Site.epi] at hF
      · exact hF
      · obtain ⟨R, bal, h, -⟩ := hF; exact ⟨R, bal, h⟩
    refine Epilogue.fits_next_write (ent := fun _ => .pred false) hC ?_ hF hE hc
    rcases hq with rfl | rfl <;> simp [Site.epi]

/-- The scan state, coordinates and setup across the request's first two reads. -/
theorem succ_q {d : D} {e : Event} {c : Epilogue.D} (hq : d.site = .q0 ∨ d.site = .q1)
    (hc : Epilogue.succ p L g (toE d) e = some (some c)) :
    coords p L g { c with site := d.v.sc.site } = coords p L g d.v.sc := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, k⟩ := e
  rcases hq with h | h <;> simp only at h <;> subst h <;>
    cases k <;> simp only [Epilogue.succ, Site.epi, reduceCtorEq] at hc
  all_goals (split at hc <;> simp only [Epilogue.word32, reduceCtorEq] at hc
             split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc
             subst hc; rfl)

set_option maxHeartbeats 4000000 in
/-- **A scheduler step keeps the reference values.** -/
theorem lfits_sched {d d' : D} {e : Event} {ns nv nc : Nat} (hs : d.site.sched = true)
    (hF : LFits p L g d ns nv nc) (hE : LExpect p L g d ns nc e) (hev : Ev p L g w d e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  rw [cm_sched hs hev, Nat.add_zero]
  rw [succ_scan hs] at hn
  obtain ⟨c, hc, rfl⟩ : ∃ c, Epilogue.succ p L g (toE d) e = some (some c) ∧ d' = ofE d c := by
    rcases h : Epilogue.succ p L g (toE d) e with _ | _ | c <;> rw [h] at hn <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hn
    exact ⟨c, rfl, hn.symm⟩
  obtain ⟨hb, hl, hqq, hq0⟩ := succ_back hs hc
  obtain ⟨h0, hFd, h1, h2⟩ := sched_fits hs hF
  have hC := efits_sched hs hFd (lexpect_sched hs hE) hev hc
  have hns : ns + Epilogue.sh e - 32 * nc = ns - 32 * nc + Epilogue.sh e := by
    unfold Epilogue.sh; split <;> omega
  rw [← hns] at hC
  have hsu := ofE_su d c
  have hco' := ofE_co d c
  have hsc' := ofE_sc d c
  obtain ⟨cs, rest⟩ := c
  cases cs <;> simp only [Mma.backE, Bool.false_eq_true, decide_eq_true_eq] at hb
  case exit l =>
    unfold LFits
    dsimp only [Site.ofE, lc]
    refine ⟨l, by unfold Epilogue.sh; split <;> omega, ?_, fun hl' => ?_, fun hl' => ?_⟩
    · exact hC
    · subst hl'; rw [hsu]; exact h2 (by rw [← hl]; rfl)
    · subst hl'; exact (h1 (by rw [← hl]; rfl)).1
  case q0 => exact absurd rfl hq0
  case q1 | ready st =>
    all_goals try subst hb
    all_goals simp only [Mma.lateE] at hl
    obtain ⟨hnc, hco⟩ := h1 hl.symm
    subst hnc
    unfold LFits
    dsimp only [Site.ofE, lc]
    refine ⟨rfl, ?_, ?_⟩
    · rw [toE_ofE (by simp [Mma.backE]) (fun _ h => by cases h)]
      simpa only [Nat.mul_zero, Nat.sub_zero] using hC
    simp only [vOf]
    have hq : d.site = .q0 ∨ d.site = .q1 := hqq (by simp)
    have hcq := succ_q hq hc
    simp only at hcq
    rw [hcq]
    exact hco (by rcases hq with h | h <;> rw [h] <;> rfl)
  all_goals
    simp only [Mma.lateE] at hl
    unfold LFits
    dsimp only [Site.ofE, lc]
    split_ifs with hlt <;> dsimp only
    · refine ⟨by omega, ?_, by rw [hsu]; exact (h2 (by rw [← hl]; exact hlt)).1,
        by rw [hsu]; exact (h2 (by rw [← hl]; exact hlt)).2⟩
      rw [toE_ofE (by simp [Mma.backE]) (fun _ h => by cases h)]; exact hC
    · have := (h1 (by rw [← hl]; simpa using hlt)).1
      subst this
      refine ⟨rfl, ?_⟩
      rw [toE_ofE (by simp [Mma.backE]) (fun _ h => by cases h)]
      simpa only [Nat.mul_zero, Nat.sub_zero] using hC

theorem epi_blk {s : Site} (h : s.blk = true) : s.epi = .ready 0 := by
  cases s <;> simp_all [Site.blk, bc, Site.epi]

/-- The rounds conjuncts carry over a step that keeps the block, the round and the setup. -/
theorem roundsB_step {o : Option Blk} {ib nc c : Nat} {v v' : V} (hr : v'.rnd = v.rnd)
    (hu : v'.su = v.su) (h : RoundsB o ib v nc) : RoundsB o (ib + c) v' (nc + c) := by
  unfold RoundsB at h ⊢
  rw [hr, hu]
  split at h
  · omega
  · obtain ⟨r, h1, h2, h3, h4⟩ := h; exact ⟨r, h1, h2, h3, by omega⟩
  · obtain ⟨r, h1, h2, h3, h4⟩ := h; exact ⟨r, h1, h2, h3, by omega⟩
  · exact ⟨h.1, h.2.1, by omega⟩
  · trivial

theorem lfits_blk_of {d : D} {ns nv nc : Nat} (hb : d.site.blk = true)
    (hF : LFits p L g d ns nv nc) :
    32 * nc + pktSh d.site ≤ ns ∧
      Epilogue.Fits p L g (toE d) (ns - 32 * nc - pktSh d.site) nv ∧ SuRef p L g d.v ∧
      Rounds d.site d.v nc ∧ PgOk p L g d := by
  unfold LFits at hF; rw [lc_blk.mpr hb] at hF; exact hF

theorem lfits_blk_mk {d : D} {ns nv nc : Nat} (hb : d.site.blk = true)
    (h : 32 * nc + pktSh d.site ≤ ns ∧
      Epilogue.Fits p L g (toE d) (ns - 32 * nc - pktSh d.site) nv ∧ SuRef p L g d.v ∧
      Rounds d.site d.v nc ∧ PgOk p L g d) : LFits p L g d ns nv nc := by
  unfold LFits; rw [lc_blk.mpr hb]; exact h

/-- **A step inside a block keeps the reference values.** -/
theorem lfits_blk {d d' : D} {e : Event} {ns nv nc : Nat} (hb : d.site.blk = true)
    (hx : d.site.blkEnd = false) (hF : LFits p L g d ns nv nc) (hev : Ev p L g w d e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := blk_step hb hx hev hn
  obtain ⟨f1, f2, f3, ⟨r1, r2⟩, ⟨⟨v₀, q1, q2, q3⟩, q4, q5, -⟩⟩ := lfits_blk_of hb hF
  have hb' : d'.site.blk = true := by simp only [Site.blk, h4]; exact hb
  have hE : toE d' = toE d := by simp only [toE, h1, epi_blk hb, epi_blk hb']
  refine lfits_blk_mk hb' ⟨by omega, ?_, by unfold SuRef; rw [h2]; exact f3, ⟨?_, ?_⟩,
    ⟨v₀, by rw [h2, q1], by rw [h8, q2], by rw [h1, q3]⟩, by rw [h8, h1, q4],
    fun hp => by rw [h9, h2]; exact q5 (by rw [← h4]; exact hp), h10⟩
  · rw [hE, h7, Nat.add_zero, show ns + Epilogue.sh e - 32 * (nc + cm e) - pktSh d'.site =
      ns - 32 * nc - pktSh d.site by omega]
    exact f2
  · rw [h2]; exact r1
  · rw [h4, h6]; exact roundsB_step h3 h2 r2

set_option maxHeartbeats 4000000 in
/-- **The reference values after the end of a block**: in the next block, or at the start of the
second pass with all the tile's packets. -/
theorem lfits_after {d d' : D} {ns nv nc : Nat} (hb : d.site.blk = true) (h0 : pktSh d.site = 0)
    (hF : LFits p L g d ns nv nc) (hA : AfterBlk (p := p) (L := L) (g := g) d d' nc) :
    LFits p L g d' ns nv nc := by
  obtain ⟨f1, f2, f3, -, ⟨⟨v₀, q1, q2, q3⟩, q4, -, -⟩⟩ := lfits_blk_of hb hF
  rw [h0, Nat.add_zero, Nat.sub_zero] at *
  rcases hA with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ | ⟨s, v', rfl, a1, a2, a3⟩
  · refine lfits_blk_mk a3 ⟨by omega, ?_, by unfold SuRef; rw [a2]; exact f3, a4,
      ⟨v₀, by rw [a2, q1], by rw [a6, q2], by rw [a1, q3]⟩, by rw [a6, a1, q4], fun _ => a7, a8⟩
    have hE : toE d' = toE d := by simp only [toE, a1, epi_blk hb, epi_blk a3]
    rw [hE, a5, Nat.sub_zero]; exact f2
  · have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal (toE d) (ns - 32 * nc) nv := by
      have := f2
      simp only [Epilogue.Fits, toE, epi_blk hb] at this
      obtain ⟨R, bal, hC, -⟩ := this
      exact ⟨R, bal, hC⟩
    obtain ⟨R, bal, hC⟩ := hC
    have hP2 := Epilogue.fits_pass2 (p := p) (L := L) (g := g) hC
    have hps : passStart p L g true (D.mk' s v') =
        if scmp .gt .s (Epilogue.laneW L g) (Epilogue.paramW p.batch) = true then
          D.mk' (.down .second) { v' with sc := { v'.sc with w := i32 0 } }
        else D.mk' (.word .second) v' := rfl
    rw [hps]
    by_cases hc : scmp .gt .s (Epilogue.laneW L g) (Epilogue.paramW p.batch) = true
    · rw [ite_eq_left hc]; rw [ite_eq_left hc] at hP2
      unfold LFits; dsimp only [lc, D.mk', Epilogue.Scan.late]
      refine ⟨f1, ?_, by unfold SuRef; rw [a2]; exact f3, by rw [a2]; exact a3⟩
      simpa only [toE, Site.epi, a1] using hP2
    · rw [ite_eq_right hc]; rw [ite_eq_right hc] at hP2
      unfold LFits; dsimp only [lc, D.mk', Epilogue.Scan.late]
      refine ⟨f1, ?_, by unfold SuRef; rw [a2]; exact f3, by rw [a2]; exact a3⟩
      simpa only [toE, Site.epi, a1] using hP2

set_option maxHeartbeats 4000000 in
/-- **The end of a block keeps the reference values.** -/
theorem lfits_end {d d' : D} {e : Event} {ns nv nc : Nat} (hb : d.site.blk = true)
    (hx : d.site.blkEnd = true) (hF : LFits p L g d ns nv nc) (hev : Ev p L g w d e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  obtain ⟨-, -, -, ⟨r1, r2⟩, ⟨-, -, q56, -⟩⟩ := lfits_blk_of hb hF
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  have hz : ∀ k : Kind, (∀ m a b c r o, k ≠ .shfl m a b c r o) → (∀ m a b, k ≠ .vote m a b) →
      (∀ md m a b, k ≠ .voteMode md m a b) → k ≠ .asyncCommit →
      Epilogue.sh ⟨pc, k⟩ = 0 ∧ Epilogue.vt ⟨pc, k⟩ = 0 ∧ cm ⟨pc, k⟩ = 0 := by
    intro k hk hv hw hc
    cases k
    case shfl => exact absurd rfl (hk _ _ _ _ _ _)
    case vote => exact absurd rfl (hv _ _ _)
    case voteMode => exact absurd rfl (hw _ _ _ _)
    case asyncCommit => exact absurd rfl hc
    all_goals simp [Epilogue.sh, Epilogue.vt, Execution.isShfl, isFullVote, voteClass, cm]
  cases s <;> simp only [Site.blkEnd, decide_eq_true_eq, Bool.false_eq_true] at hx
  case arrive per b =>
    subst hx
    simp only [Ev] at hev
    subst hev
    obtain ⟨z1, z2, z3⟩ := hz (Kind.asyncArrive _ _) (fun _ _ _ _ _ _ h => Kind.noConfusion h)
      (fun _ _ _ h => Kind.noConfusion h) (fun _ _ _ _ h => Kind.noConfusion h)
      (fun h => by cases h)
    rw [z1, z2, z3]; simp only [Nat.add_zero]
    simp only [succ, afterArrive, Option.some.injEq] at hn
    subst hn
    refine lfits_after hb rfl hF ?_
    cases per <;> simp only [afterArrive]
    · exact after_prime r1 (by simpa [RoundsB, bc, inBlk] using r2)
    · simp only [RoundsB, bc, inBlk] at r2
      obtain ⟨r, h1, h2, h3, h4⟩ := r2
      exact warm_end r1 (q56 (by simp [bc])) h1 h2 h3 h4
    · simp only [RoundsB, bc, inBlk] at r2
      obtain ⟨r, h1, h2, h3, h4⟩ := r2
      exact steady_end r1 (q56 (by simp [bc])) h1 h2 h3 h4
  case te t i =>
    obtain ⟨ht, hi⟩ := hx
    have : t = 6 := Fin.ext ht
    subst this
    have : i = 2 := Fin.ext hi
    subst this
    simp only [Ev] at hev
    rcases hev with ⟨inst, ld, -, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> simp only [succ] at hn
    · obtain ⟨z1, z2, z3⟩ := hz (Kind.elect _ _ _) (fun _ _ _ _ _ _ h => Kind.noConfusion h)
        (fun _ _ _ h => Kind.noConfusion h) (fun _ _ _ _ h => Kind.noConfusion h)
        (fun h => by cases h)
      rw [z1, z2, z3]; simp only [Nat.add_zero]
      simp only [Option.some.injEq] at hn
      split at hn
      · subst hn
        refine lfits_blk_mk (by rfl) ?_
        obtain ⟨f1, f2, f3, -, ⟨q1, q2, -, -⟩⟩ := lfits_blk_of hb hF
        exact ⟨f1, f2, f3, ⟨r1, r2⟩, q1, q2, fun _ => q56 (by simp [bc]), fun _ _ h => by cases h⟩
      · subst hn
        refine lfits_after hb rfl hF ?_
        simp [RoundsB, bc, inBlk] at r2
        exact after_tail r1 (q56 (by simp [bc])) (by rw [r2.2.2, w0_of r2.2.1])
    · cases hn
  case tc t c =>
    obtain ⟨ht, hc⟩ := hx
    have : t = 6 := Fin.ext ht
    subst this
    have : c = 1 := Fin.ext hc
    subst this
    have hzz : Epilogue.sh ⟨pc, kind⟩ = 0 ∧ Epilogue.vt ⟨pc, kind⟩ = 0 ∧ cm ⟨pc, kind⟩ = 0 := by
      simp only [Ev] at hev
      rcases hev with ⟨a, sp, hk, -⟩ | ⟨f, hk⟩ <;> rw [hk]
      · exact hz (Kind.tensorIssue _ _) (fun _ _ _ _ _ _ h => Kind.noConfusion h)
          (fun _ _ _ h => Kind.noConfusion h) (fun _ _ _ _ h => Kind.noConfusion h)
          (fun h => by cases h)
      · exact hz (Kind.ub _) (fun _ _ _ _ _ _ h => Kind.noConfusion h)
          (fun _ _ _ h => Kind.noConfusion h) (fun _ _ _ _ h => Kind.noConfusion h)
          (fun h => by cases h)
    rw [hzz.1, hzz.2.1, hzz.2.2]; simp only [Nat.add_zero]
    simp only [succ, Option.some.injEq, Fin.isValue, Fin.val_one, one_ne_zero,
      ↓reduceIte] at hn
    subst hn
    refine lfits_after hb rfl hF ?_
    simp [RoundsB, bc, inBlk] at r2
    exact after_tail r1 (q56 (by simp [bc])) (by rw [r2.2.2, w0_of r2.2.1])

/-- The output-warp state after the tile count `x` of the first pass. -/
def tilesE (p : Params) (d : D) (x : BitVec 64) : Epilogue.D := Epilogue.tilesD p (toE d) x

/-- **The choice of a tile**: the successor holds the output warp's scan state after the tile
count, at the request's first read with the tile's coordinates, or at the drain. -/
theorem succ_tiles {d d' : D} {e : Event} (hs : d.site = .tiles false)
    (hn : succ p L g w d e = some (some d')) :
    ∃ x : BitVec 64, (∃ pc r a b c ok, e = ⟨pc, .shfl r a b c (.bits 32 x) ok⟩) ∧
      d'.v.sc = { tilesE p d x with site := d.v.sc.site } ∧ d'.v.su = d.v.su ∧
      (((tilesE p d x).site = .q0 ∧ d'.site = .q0 ∧ d'.v.co = coords p L g d'.v.sc) ∨
      ((tilesE p d x).site = .exit false ∧ d'.site = .dw 0)) := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hs
  subst hs
  cases kind <;> simp only [succ, reduceCtorEq] at hn
  case shfl r a b c wv ok =>
    cases wv
    all_goals try (simp at hn; done)
    case bits n x =>
      by_cases h32 : n = 32
      · subst h32
        refine ⟨x, ⟨pc, r, a, b, c, ok, rfl⟩, ?_⟩
        simp only [afterTiles, Bool.false_eq_true, ↓reduceIte] at hn
        repeat' split at hn
        all_goals simp only [Option.map_some, Option.map_none, reduceCtorEq,
          Option.some.injEq] at hn
        all_goals subst hn
        all_goals simp only [D.ite]
        all_goals split <;> rename_i hch <;>
          simp_all [tilesE, Epilogue.tilesD, toE, Site.epi, scAt, drain0, chosen]
      · simp [h32] at hn

set_option maxHeartbeats 4000000 in
/-- **The first pass's choice of a tile keeps the reference values.** -/
theorem lfits_tiles {d d' : D} {e : Event} {ns nv nc : Nat} (hs : d.site = .tiles false)
    (hF : LFits p L g d ns nv nc) (hE : LExpect p L g d ns nc e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  obtain ⟨x, ⟨pc, r, a, b, c, ok, rfl⟩, hsc, hsu, hq⟩ := succ_tiles hs hn
  have hF' := hF
  unfold LFits at hF'
  rw [hs] at hF'
  simp only [lc, Bool.false_eq_true, ↓reduceIte] at hF'
  obtain ⟨rfl, hFit⟩ := hF'
  have hExp : Epilogue.Expect p L g (toE d) ns ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ := by
    have := hE
    obtain ⟨s, v, kk⟩ := d
    simp only at hs; subst hs
    simpa [LExpect, Site.sched, Site.scan] using this
  have hts : (toE d).site = .tiles false := by simp [toE, hs, Site.epi]
  have hT := Epilogue.fits_tilesD hts hFit (x := x) fun R n0 v0 hP hEnd => by
    have hse : d.site.epi = .tiles false := by simp [hs, Site.epi]
    simp only [Epilogue.Expect, toE, hse] at hExp
    have := hExp R n0 v0 hP hEnd
    simp only [Value.bits.injEq, true_and] at this
    rw [this]; rfl
  have hsh : Epilogue.sh ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 1 := rfl
  have hvt : Epilogue.vt ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 0 := rfl
  have hcm : cm ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 0 := rfl
  rw [hsh, hvt, hcm, Nat.add_zero, Nat.add_zero]
  rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · unfold LFits; rw [h2]; dsimp only [lc]
    refine ⟨rfl, ?_, h3⟩
    have : toE d' = tilesE p d x := by
      simp only [toE, h2, Site.epi, hsc]; rw [← h1]
    rw [this]; exact hT
  · unfold LFits; rw [h2]; dsimp only [lc]
    refine ⟨false, by omega, ?_, fun h => absurd h (by decide), fun _ => rfl⟩
    rw [hsc, ← h1]; exact hT

set_option maxHeartbeats 4000000 in
/-- **The second pass's last shuffle leads to the drain** with the reference values of the
output warp's return. -/
theorem lfits_tiles2 {d d' : D} {e : Event} {ns nv nc : Nat} (hs : d.site = .tiles true)
    (hF : LFits p L g d ns nv nc) (hE : LExpect p L g d ns nc e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  obtain ⟨s, v, kk⟩ := d
  simp only at hs; subst hs
  unfold LFits at hF; dsimp only [lc] at hF
  obtain ⟨h0, hFit, hsu, hpk⟩ := hF
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [succ, reduceCtorEq] at hn
  case shfl r a b c wv ok =>
    cases wv <;> try (simp at hn; done)
    rename_i n x
    by_cases h32 : n = 32
    · subst h32
      simp only [↓reduceIte, Option.some.injEq] at hn
      subst hn
      have hExp : Epilogue.Expect p L g (toE ⟨.tiles true, v, kk⟩) (ns - 32 * nc)
          ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ := by
        simpa [LExpect, Site.sched, Site.scan] using hE
      have hT := Epilogue.fits_next_tiles (ent := fun _ => .pred false) (late := true)
        (d := toE ⟨.tiles true, v, kk⟩) (by rfl) hFit hExp rfl
      have hsh : Epilogue.sh ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 1 := rfl
      have hvt : Epilogue.vt ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 0 := rfl
      have hcm : cm ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 0 := rfl
      rw [hsh, hvt, hcm, Nat.add_zero, Nat.add_zero]
      unfold LFits; dsimp only [lc, scAt, D.mk']
      refine ⟨true, by omega, ?_, fun _ => ⟨hsu, hpk⟩, fun h => absurd h (by decide)⟩
      convert hT using 2
      omega
    · simp [h32] at hn

/-- The drain's steps keep the scan state and the setup and fire no shuffle, ballot or commit. -/
theorem lfits_drain {d d' : D} {e : Event} {ns nv nc : Nat} (hs : lc d.site = .drain)
    (hF : LFits p L g d ns nv nc) (hev : Ev p L g w d e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [lc, reduceCtorEq] at hs <;> (try split at hs <;> cases hs)
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals simp only [succ, dwNext, D.ite, reduceCtorEq, Option.some.injEq] at hn
  all_goals (repeat' split at hn)
  all_goals try subst hn
  all_goals first
    | (cases hn; done)
    | (simp only [Epilogue.sh, Epilogue.vt, Execution.isShfl, isFullVote, voteClass, cm,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
       unfold LFits at hF ⊢
       first | exact hF | (rename_i k; fin_cases k <;> exact hF) | skip)

theorem setup_r28 {v1 v2 : V} (hco : v1.co.row = v2.co.row) (hu : v1.ukw = v2.ukw)
    (h0 : v1.sc.c0 = v2.sc.c0) (h1 : v1.sc.c1 = v2.sc.c1) :
    (setup p L g v1).r28 = (setup p L g v2).r28 := by
  simp only [setup, hco, hu, h0, h1]

theorem setup_r31 (v : V) : (setup p L g v).r31 = addi (setup p L g v).r28 (-1) := by
  simp only [setup]

set_option maxHeartbeats 4000000 in
/-- **The used-K read starts the first block** with the picked tile's block word. -/
theorem lfits_uk {d d' : D} {e : Event} {ns nv nc : Nat} (hs : d.site = .uk)
    (hF : LFits p L g d ns nv nc) (hE : LExpect p L g d ns nc e) (hev : Ev p L g w d e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  obtain ⟨s, v, kk⟩ := d
  simp only at hs; subst hs
  unfold LFits at hF; dsimp only [lc] at hF
  obtain ⟨rfl, hFit, hco⟩ := hF
  obtain ⟨pc, kind⟩ := e
  simp only [Ev] at hev
  rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> simp only [succ, reduceCtorEq] at hn
  simp only [LExpect] at hE
  rw [hE] at hn
  simp only [word32, Option.some.injEq] at hn
  subst hn
  have hz : Epilogue.sh ⟨pc, .rd (wordAcc (rv p L g w ⟨.uk, v, kk⟩ (reqRegs .uk).1 +
      BitVec.ofInt 64 (reqRegs .uk).2).toNat) bs⟩ = 0 ∧ Epilogue.vt ⟨pc, .rd (wordAcc
      (rv p L g w ⟨.uk, v, kk⟩ (reqRegs .uk).1 + BitVec.ofInt 64 (reqRegs .uk).2).toNat) bs⟩ = 0 ∧
      cm ⟨pc, .rd (wordAcc (rv p L g w ⟨.uk, v, kk⟩ (reqRegs .uk).1 +
      BitVec.ofInt 64 (reqRegs .uk).2).toNat) bs⟩ = 0 := ⟨rfl, rfl, rfl⟩
  rw [hz.1, hz.2.1, hz.2.2]
  simp only [Nat.add_zero, Nat.mul_zero]
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ :=
    pgEnter_props (p := p) (L := L) (g := g)
      (D.mk' .uk (withSetup p L g { v with ukw := ukv p (chosen v.sc) })) .prime 0
  have hb : (pgEnter p L g (D.mk' .uk (withSetup p L g { v with ukw := ukv p (chosen v.sc) }))
      .prime 0).site.blk = true := by simp only [Site.blk, p4]; rfl
  obtain ⟨p7, p8⟩ := pgEnter_v (p := p) (L := L) (g := g)
    (D.mk' .uk (withSetup p L g { v with ukw := ukv p (chosen v.sc) })) .prime 0
  refine lfits_blk_mk hb ⟨by rw [p6]; omega, ?_, ?_, ⟨?_, ?_⟩,
    ⟨{ v with ukw := ukv p (chosen v.sc) }, p2, p7.symm, p1.symm⟩, by rw [p7, p1],
    fun h => absurd (p4.trans rfl) h, pgEnter_row _ _ _⟩
  · have : toE (pgEnter p L g (D.mk' .uk (withSetup p L g { v with ukw := ukv p (chosen v.sc) }))
        .prime 0) = toE ⟨.uk, v, kk⟩ := by
      simp only [toE]; rw [p1, epi_blk hb]; rfl
    rw [this, p6]; simpa using hFit
  · -- the block word is the picked tile's
    have hFit' := hFit
    simp only [Epilogue.Fits, toE, Site.epi] at hFit'
    obtain ⟨R, bal, hC, hc0, hc1⟩ := hFit'
    refine ⟨R, bal, hC.1, ?_⟩
    rw [p2]
    obtain ⟨hPk, htot, hgx, hcur, hbal, hpv, hnt, -, -⟩ := id hC
    simp only [chosen] at htot hgx hcur hbal hpv hnt hc0 hc1
    have hch : chosen v.sc = chosen (Epilogue.chosenD p (g / L.block) R bal) := by
      simp only [chosen, hgx, hbal, Epilogue.chosenD]
    have hcoE : coords p L g v.sc = coords p L g (refVL p L g R bal).sc := by
      simp only [coords, refVL, htot, hcur, hpv, hnt, Epilogue.chosenD]
    simp only [D.mk', withSetup, r28Ref]
    apply setup_r28
    · simp only [hco, hcoE, refVL]
    · simp only [refVL, hch]
    · simp only [refVL, hc0]; exact congrArg (qv p) hch
    · simp only [refVL, hc1]; exact congrArg (fun z => qv p (addi z 1)) hch
  · rw [p2]; exact setup_r31 _
  · rw [p4, p5]; simp only [RoundsB, bc, p2, p3]

set_option maxHeartbeats 4000000 in
/-- **The `setmaxnreg` leads to the scan's first round** with the output warp's first values. -/
theorem lfits_setmax {d d' : D} {e : Event} {ns nv nc : Nat} (hs : d.site = .setmax)
    (hF : LFits p L g d ns nv nc) (hev : Ev p L g w d e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  obtain ⟨s, v, kk⟩ := d
  simp only at hs; subst hs
  unfold LFits at hF; dsimp only [lc] at hF
  obtain ⟨rfl, rfl, rfl⟩ := hF
  simp only [Ev] at hev
  obtain ⟨inc, n, inst, hk⟩ := hev
  obtain ⟨pc, kind⟩ := e
  simp only at hk; subst hk
  simp only [succ, Option.some.injEq] at hn
  subst hn
  have h0 := Epilogue.fits_next_start (p := p) (L := L) (g := g) (ent := fun _ => .pred false)
    (d := toE ⟨.setmax, v, kk⟩) (e := ⟨0, .exit⟩) (ns := 3) (nv := 0) (by simp [Site.epi])
    (by simp [Epilogue.Fits, Site.epi]) rfl
  have hz : Epilogue.sh ⟨pc, .setMaxReg inc n inst⟩ = 0 ∧
      Epilogue.vt ⟨pc, .setMaxReg inc n inst⟩ = 0 ∧
      cm ⟨pc, .setMaxReg inc n inst⟩ = 0 := ⟨rfl, rfl, rfl⟩
  rw [hz.1, hz.2.1, hz.2.2]
  simp only [passStart, Bool.false_eq_true, ↓reduceIte, D.ite] at h0 ⊢
  split <;> rename_i hb <;> simp only [hb, ↓reduceIte] at h0 <;>
    (unfold LFits; dsimp only [lc, scAt, D.mk', Epilogue.Scan.late]) <;>
    exact ⟨rfl, by simpa [toE, Site.epi] using h0⟩

/-- **Every step of a loader lane on an event that returns what the reference says keeps the
reference values**, with the shuffle, ballot and commit it adds. -/
theorem lfits_next {d d' : D} {e : Event} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc)
    (hE : LExpect p L g d ns nc e) (hev : Ev p L g w d e)
    (hn : succ p L g w d e = some (some d')) :
    LFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) (nc + cm e) := by
  by_cases hs : d.site.sched = true
  · exact lfits_sched hs hF hE hev hn
  by_cases ht : d.site = .tiles false
  · exact lfits_tiles ht hF hE hn
  by_cases ht2 : d.site = .tiles true
  · exact lfits_tiles2 ht2 hF hE hn
  by_cases hu : d.site = .uk
  · exact lfits_uk hu hF hE hev hn
  by_cases hm : d.site = .setmax
  · exact lfits_setmax hm hF hev hn
  by_cases hb : d.site.blk = true
  · cases hx : d.site.blkEnd
    · exact lfits_blk hb hx hF hev hn
    · exact lfits_end hb hx hF hev hn
  · apply lfits_drain _ hF hev hn
    obtain ⟨s, v, kk⟩ := d
    cases s <;> simp_all [Site.sched, Site.blk, bc, lc]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
