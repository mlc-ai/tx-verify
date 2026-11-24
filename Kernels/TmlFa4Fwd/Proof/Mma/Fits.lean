-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
public import Kernels.TmlFa4Fwd.Proof.Mma.Ledger
public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Sim
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's reference values

The MMA warp's scheduler is the output warp's on its scan state, so its reference values are the
output warp's (`Epilogue.Fits`) on `toE d`, with the thread's shuffle count shifted: by the
broadcast before the scan (one shuffle) and the pipeline's broadcasts so far (the ghost count
`v.ps`). Before the broadcast the warp is at shuffle 3 with no ballot. In the pipeline the
request's used-K length is the launch word (`ukv`), and in the second pass the pipeline's
broadcasts are the full pipeline's of the picked tile (`pipeN`), a function of the first pass's
choice; this is what makes the second pass's positions the same on every lane (`MFits`).

`mfits_next`: a step on an event that returns what the reference says (`MExpect`) keeps
`MFits`. At a scheduler site it is the output warp's step (`succ_scan`, `Epilogue.fits_next`);
the choice of a tile is `Epilogue.fits_tilesD`, the second pass's start `Epilogue.fits_pass2`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (laneW paramW chosen Picked)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The pipeline's values of the tile the first pass picked after its scan ended at round `R`
with ballot `bal`. -/
def refV (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : V :=
  let c := Epilogue.chosenD p (g / L.block) R bal
  { sc := { c with c0 := Epilogue.qv p (chosen c), c1 := Epilogue.qv p (addi (chosen c) 1) },
    ukw := ukv p (chosen c) }

/-- The pipeline's broadcasts of the picked tile: three, six per loop round, five in the tail. -/
def pipeN (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : Nat :=
  shAt 100 (Bs p L g (refV p L g R bal) - 1).toNat

/-- **The reference values at a state of an MMA lane**, with the thread's shuffles `ns` and
full-mask ballots `nv` before it. -/
def MFits (p : Params) (L : Launch) (g : Nat) (d : D) (ns nv : Nat) : Prop :=
  if d.site.early then ns = 3 ∧ nv = 0 ∧ d.v.ps = 0 else
    d.v.ps + 1 ≤ ns ∧ Epilogue.Fits p L g (toE d) (ns - 1 - d.v.ps) nv ∧
      (d.site.pipe = true → d.v.ukw = ukv p (chosen d.v.sc)) ∧
      (d.site.late = true → ∃ R bal, Picked p L g R bal ∧ d.v.ps = pipeN p L g R bal) ∧
      (d.site.pipe = false → d.site.late = false → d.v.ps = 0)

/-- What the reference says an event at an MMA state returns: the output warp's reference at a
scheduler site, the launch's used-K length at its read, and a word at a broadcast. -/
def MExpect (p : Params) (L : Launch) (g : Nat) (d : D) (ns : Nat) (e : Event) : Prop :=
  match d.site, e.kind with
  | .uk, .rd _ bs => rebuild 3 bs = .ok (.bits 32 (ukv p (chosen d.v.sc)))
  | .bcast, .shfl _ _ _ _ v _ | .sh _, .shfl _ _ _ _ v _ => ∃ x, v = .bits 32 x
  | s, _ => (s.sched || s == .tiles false) = true →
      Epilogue.Expect p L g (toE d) (ns - 1 - d.v.ps) e

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ns nv : Nat}

/-! ### Output-warp sites that are MMA sites -/

theorem ofE_back {s : Epilogue.Site} (h : backE s = true) :
    (Site.ofE s).epi = s ∧ (Site.ofE s).late = lateE s ∧ (Site.ofE s).pipe = false ∧
      (Site.ofE s).early = false := by
  cases s <;> simp_all [backE, Site.ofE, Site.epi, Site.late, lateE, Site.pipe, Site.early]

theorem toE_ofE {d : D} {c : Epilogue.D} (h : backE c.site = true) : toE (ofE d c) = c := by
  simp only [toE, (ofE_back h).1]

/-- **A scheduler step reaches a scheduler site, a read, or the end**, in the same pass. -/
theorem succ_back {d : D} {e : Event} {c : Epilogue.D} (hs : d.site.sched = true)
    (h : Epilogue.succ p L g (toE d) e = some (some c)) :
    backE c.site = true ∧ lateE c.site = d.site.late := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.sched, Bool.false_eq_true] at hs
  all_goals try subst hs
  all_goals cases kind <;> simp only [Epilogue.succ, Site.epi, reduceCtorEq] at h
  all_goals try simp only [Epilogue.word32, Epilogue.afterTotal, Epilogue.loopHead,
    Epilogue.scanExit] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq, Option.some.injEq] at h
  all_goals first
    | (subst h; simp_all [backE, lateE, Site.late, Epilogue.loopOf, Epilogue.Scan.late]; done)
    | (cases h; done)
    | (simp_all; done)

theorem mexpect_sched {d : D} {e : Event} (hs : (d.site.sched || d.site == .tiles false) = true)
    (hE : MExpect p L g d ns e) : Epilogue.Expect p L g (toE d) (ns - 1 - d.v.ps) e := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, k⟩ := e
  cases s <;> simp only [MExpect] at hE <;> first | exact hE hs | simp [Site.sched] at hs

theorem sched_early {s : Site} (hs : (s.sched || s == .tiles false) = true) :
    s.early = false ∧ s.pipe = false := by
  cases s <;> simp_all [Site.sched, Site.early, Site.pipe]

/-- An MMA state that is not before the scan. -/
theorem mfits_main {d : D} (h : d.site.early = false) (hF : MFits p L g d ns nv) :
    d.v.ps + 1 ≤ ns ∧ Epilogue.Fits p L g (toE d) (ns - 1 - d.v.ps) nv ∧
      (d.site.pipe = true → d.v.ukw = ukv p (chosen d.v.sc)) ∧
      (d.site.late = true → ∃ R bal, Picked p L g R bal ∧ d.v.ps = pipeN p L g R bal) ∧
      (d.site.pipe = false → d.site.late = false → d.v.ps = 0) := by
  simpa only [MFits, h, Bool.false_eq_true, ↓reduceIte] using hF

/-- The reference values at a state reached by a scheduler step. -/
theorem mfits_ofE {d : D} {c : Epilogue.D} {ns' nv' : Nat} (hb : backE c.site = true)
    (hl : lateE c.site = d.site.late) (hd : d.site.early = false ∧ d.site.pipe = false)
    (hF : MFits p L g d ns nv) (hns : d.v.ps + 1 ≤ ns')
    (hc : Epilogue.Fits p L g c (ns' - 1 - d.v.ps) nv') : MFits p L g (ofE d c) ns' nv' := by
  obtain ⟨-, -, -, hlate, h0⟩ := mfits_main hd.1 hF
  obtain ⟨he, hl', hp, hy⟩ := ofE_back hb
  simp only [MFits, ofE] at hp hy hl' ⊢
  simp only [hy, Bool.false_eq_true, ↓reduceIte]
  refine ⟨hns, by rw [toE_ofE hb]; exact hc, fun h => by simp [hp] at h, fun h => ?_,
    fun _ h => h0 hd.2 (by rw [← hl, ← hl']; exact h)⟩
  exact hlate (by rw [← hl, ← hl']; exact h)

set_option maxHeartbeats 4000000 in
/-- **A scheduler step keeps the reference values.** -/
theorem mfits_sched {d d' : D} {e : Event} (hs : d.site.sched = true)
    (hF : MFits p L g d ns nv) (hE : MExpect p L g d ns e) (hev : Ev p L g d e)
    (hn : succ p L g d e = some (some d')) :
    MFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  rw [succ_scan hs] at hn
  obtain ⟨c, hc, rfl⟩ : ∃ c, Epilogue.succ p L g (toE d) e = some (some c) ∧ d' = ofE d c := by
    rcases h : Epilogue.succ p L g (toE d) e with _ | _ | c <;> rw [h] at hn <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hn
    exact ⟨c, rfl, hn.symm⟩
  obtain ⟨hb, hl⟩ := succ_back hs hc
  have hd := sched_early (s := d.site) (by simp [hs])
  obtain ⟨hps, hFit, -, -, -⟩ := mfits_main hd.1 hF
  have hExp := mexpect_sched (by simp [hs]) hE
  refine mfits_ofE hb hl hd hF (by omega) ?_
  have hns : ns + Epilogue.sh e - 1 - d.v.ps = ns - 1 - d.v.ps + Epilogue.sh e := by
    unfold Epilogue.sh; split <;> omega
  rw [hns]
  by_cases hsc : d.site.scan = true
  · have hev' : Epilogue.Ev p L g (toE d) e := by
      obtain ⟨s, v⟩ := d
      cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;>
        simpa only [Ev, toE, Site.epi, Site.toE] using hev
    exact Epilogue.fits_next (ent := fun _ => .pred false) hFit hExp hev' hc
  · obtain ⟨s, v⟩ := d
    have hq : s = .q0 ∨ s = .q1 := by cases s <;> simp_all [Site.sched, Site.scan]
    have hsh : Epilogue.sh e = 0 ∧ Epilogue.vt e = 0 := by
      obtain ⟨pc, k⟩ := e
      rcases hq with rfl | rfl <;> simp only [Ev] at hev <;>
        rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> exact ⟨rfl, rfl⟩
    rw [hsh.1, hsh.2, Nat.add_zero, Nat.add_zero]
    have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal (toE ⟨s, v⟩) (ns - 1 - v.ps) nv := by
      rcases hq with rfl | rfl <;> simp only [Epilogue.Fits, toE, Site.epi] at hFit
      · exact hFit
      · obtain ⟨R, bal, h, -⟩ := hFit; exact ⟨R, bal, h⟩
    refine Epilogue.fits_next_write (ent := fun _ => .pred false) hC ?_ hFit hExp hc
    rcases hq with rfl | rfl <;> simp [Site.epi]

set_option maxHeartbeats 4000000 in
/-- **The choice of a tile keeps the reference values.** -/
theorem mfits_tiles {d d' : D} {e : Event} (hs : d.site = .tiles false)
    (hF : MFits p L g d ns nv) (hE : MExpect p L g d ns e)
    (hn : succ p L g d e = some (some d')) :
    MFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨x, ⟨pc, r, a, b, c, ok, rfl⟩, rfl⟩ := succ_tiles hs hn
  have hd := sched_early (s := d.site) (by simp [hs])
  obtain ⟨hps, hFit, -, -, -⟩ := mfits_main hd.1 hF
  have hExp := mexpect_sched (by simp [hs]) hE
  have hts : (toE d).site = .tiles false := by simp [hs, Site.epi]
  have hT := Epilogue.fits_tilesD hts hFit (x := x) fun R n0 v0 hP hEnd => by
    have hse : d.site.epi = .tiles false := by simp [hs, Site.epi]
    simp only [Epilogue.Expect, hse] at hExp
    have := hExp R n0 v0 hP hEnd
    simp only [Value.bits.injEq, true_and] at this
    rw [this]; rfl
  have hsh : Epilogue.sh ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 1 := rfl
  have hvt : Epilogue.vt ⟨pc, .shfl r a b c (.bits 32 x) ok⟩ = 0 := rfl
  rw [hsh, hvt, Nat.add_zero]
  have hns : ns + 1 - 1 - d.v.ps = ns - 1 - d.v.ps + 1 := by omega
  simp only [tilesE, Epilogue.tilesD] at hT ⊢
  split <;> rename_i hb <;> simp only [hb, ↓reduceIte] at hT <;>
    refine mfits_ofE (by simp [backE]) (by simp [lateE, hs, Site.late]) hd hF (by omega) ?_ <;>
    rw [hns] <;> exact hT

set_option maxHeartbeats 4000000 in
/-- **The broadcast before the scan leads to the scan's first round** with the output warp's
first values. -/
theorem mfits_bcast {d d' : D} {e : Event} (hs : d.site = .bcast)
    (hF : MFits p L g d ns nv) (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    MFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨s, v⟩ := d
  simp only at hs
  subst hs
  simp only [MFits, Site.early, ↓reduceIte] at hF
  obtain ⟨rfl, rfl, hps⟩ := hF
  simp only [Ev] at hev
  obtain ⟨rv, okv, he⟩ := hev
  obtain ⟨pc, kind⟩ := e
  simp only at he
  subst he
  simp only [succ, word32] at hn
  split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn
  subst hn
  have h0 := Epilogue.fits_next_start (p := p) (L := L) (g := g) (ent := fun _ => .pred false)
    (d := toE ⟨.bcast, v⟩) (e := ⟨0, .exit⟩) (ns := 3) (nv := 0) (by simp [Site.epi])
    (by simp [Epilogue.Fits, Site.epi]) rfl
  simp only [Epilogue.sh, Epilogue.vt, Execution.isShfl, isFullVote, voteClass, ↓reduceIte]
  simp only [passStart, Bool.false_eq_true, ↓reduceIte] at h0 ⊢
  split <;> rename_i hb <;> simp only [hb, ↓reduceIte] at h0 <;>
    simp only [MFits, scAt, Site.early, Site.pipe, Site.late, Epilogue.Scan.late,
      Bool.false_eq_true, ↓reduceIte, hps] <;>
    refine ⟨by omega, ?_, by simp, by simp, by simp⟩ <;>
    simpa [toE, Site.epi, voteClass] using h0

theorem pipe_late {s : Site} (h : s.pipe = true) : s.late = false := by
  cases s <;> simp_all [Site.pipe, Site.late]

/-- A step that keeps the scan state: the reference values carry over. -/
theorem mfits_keep {d d' : D} {k : Nat} (hd : d.site.early = false) (hd' : d'.site.early = false)
    (hF : MFits p L g d ns nv) (hepi : d'.site.epi = d.site.epi) (hsc : d'.v.sc = d.v.sc)
    (hps : d'.v.ps = d.v.ps + k)
    (hpipe : d'.site.pipe = true → d'.v.ukw = ukv p (chosen d.v.sc) ∨
      (d.site.pipe = true ∧ d'.v.ukw = d.v.ukw))
    (hlate : d'.site.late = d.site.late) (hpl : d'.site.pipe = false → d.site.pipe = false)
    (hk : k ≠ 0 → d'.site.pipe = true) :
    MFits p L g d' (ns + k) nv := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mfits_main hd hF
  simp only [MFits, hd', Bool.false_eq_true, ↓reduceIte]
  refine ⟨by omega, ?_, fun h => ?_, fun h => ?_, fun h h' => ?_⟩
  · have : toE d' = toE d := by simp only [toE, hepi, hsc]
    rw [this, show ns + k - 1 - d'.v.ps = ns - 1 - d.v.ps by omega]
    exact h2
  · rcases hpipe h with h' | ⟨hp, h'⟩
    · rw [h', hsc]
    · rw [h', hsc]; exact h3 hp
  · obtain ⟨R, bal, hP, he⟩ := h4 (by rw [← hlate]; exact h)
    have hk0 : k = 0 := by
      by_contra h0
      have := pipe_late (hk h0); rw [this] at h; cases h
    exact ⟨R, bal, hP, by omega⟩
  · have hk0 : k = 0 := by
      by_contra h0; rw [hk h0] at h; cases h
    rw [hps, h5 (hpl h) (by rw [← hlate]; exact h'), hk0]

/-- A pipeline site: the scan state is the request's, at the first stage poll's output-warp
site. -/
def Site.pmid (s : Site) : Prop :=
  s.epi = .ready 0 ∧ s.early = false ∧ s.pipe = true ∧ s.late = false

theorem pmid_of {s : Site} (h : s.pipe = true) : s.pmid := by
  cases s <;> simp_all [Site.pipe, Site.pmid, Site.epi, Site.early, Site.late]

theorem pmid_wtNext (k : Fin 10) : (wtNext k).pmid := pmid_of (by fin_cases k <;> rfl)
theorem pmid_shNext (k : Fin 14) : (shNext k).pmid := pmid_of (by fin_cases k <;> rfl)
theorem pmid_qkDone (b : Fin 4) : (qkDone b).pmid := pmid_of (by fin_cases b <;> rfl)
theorem pmid_pvDone (b : Fin 4) : (pvDone b).pmid := pmid_of (by fin_cases b <;> rfl)

/-- A pipeline step: the reference values carry over. -/
theorem mfits_pipe {d d' : D} {k : Nat} (h : d.site.pmid) (h' : d'.site.pmid)
    (hF : MFits p L g d ns nv) (hsc : d'.v.sc = d.v.sc) (hu : d'.v.ukw = d.v.ukw)
    (hps : d'.v.ps = d.v.ps + k) : MFits p L g d' (ns + k) nv :=
  mfits_keep h.2.1 h'.2.1 hF (h'.1.trans h.1.symm) hsc hps (fun _ => .inr ⟨h.2.2.1, hu⟩)
    (h'.2.2.2.trans h.2.2.2.symm) (fun hp => by rw [h'.2.2.1] at hp; cases hp)
    (fun _ => h'.2.2.1)

theorem pmid_ite {c : Prop} [Decidable c] {a b : Site} (ha : a.pmid) (hb : b.pmid) :
    (if c then a else b).pmid := by
  split <;> assumption

/-- The successor of commit `c` other than the last is a pipeline state over the same scan. -/
theorem ceNext_pipe {d : D} {c : Fin 12} (hc : c ≠ 11) :
    (ceNext p L g d c).site.pmid ∧ (ceNext p L g d c).v.sc = d.v.sc ∧
      (ceNext p L g d c).v.ukw = d.v.ukw ∧ (ceNext p L g d c).v.ps = d.v.ps := by
  fin_cases c <;> simp only [ceNext, enterLoop, loopEnd] <;> try split
  all_goals first
    | exact absurd rfl hc
    | (refine ⟨pmid_of rfl, ?_, ?_, ?_⟩ <;> simp)

/-- **A pipeline state holds the picked tile**, and the tile's K/V blocks are the reference
pipeline's (`refV`). -/
theorem bs_ref {d : D} (hpm : d.site.pmid) (hF : MFits p L g d ns nv) :
    ∃ R bal, Epilogue.ChosenVals p L g R bal (toE d) (ns - 1 - d.v.ps) nv ∧
      Bs p L g d.v = Bs p L g (refV p L g R bal) := by
  obtain ⟨s, v⟩ := d
  obtain ⟨-, hFit, hukw, -, -⟩ := mfits_main hpm.2.1 hF
  have hFit' := hFit
  simp only [Epilogue.Fits, toE, hpm.1] at hFit'
  obtain ⟨R, bal, hC, hc0, hc1⟩ := hFit'
  refine ⟨R, bal, hC, ?_⟩
  obtain ⟨hPk, htot, hgx, hcur, hbal, hpv, hnt, -, -⟩ := id hC
  simp only [chosen] at htot hgx hcur hbal hpv hnt hc0 hc1
  have hch : chosen v.sc = chosen (Epilogue.chosenD p (g / L.block) R bal) := by
    simp only [chosen, hgx, hbal, Epilogue.chosenD]
  have hco : coords p L g v.sc = coords p L g (refV p L g R bal).sc := by
    simp only [coords, refV, htot, hcur, hpv, hnt, Epilogue.chosenD]
  have hu : v.ukw = (refV p L g R bal).ukw := by
    rw [hukw hpm.2.2.1, hch]; rfl
  have h0 : v.sc.c0 = (refV p L g R bal).sc.c0 := by
    rw [hc0]; simp only [refV]; rw [← hch]
  have h1 : v.sc.c1 = (refV p L g R bal).sc.c1 := by
    rw [hc1]; simp only [refV]; rw [← hch]
  simp only [Bs, blocks, hco, hu, h0, h1]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
