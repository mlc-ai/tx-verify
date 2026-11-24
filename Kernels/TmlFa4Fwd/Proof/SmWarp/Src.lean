-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Read
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.SmWarp.Expect
import Lemmas.Kernel.FrameU
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
import Kernels.TmlFa4Fwd.Proof.SmWarp.Sound
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
import Lemmas.Flow.AllocTmpl
import Lemmas.Step.WarpShfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The sources of the softmax warps' scheduler values, and the never-dropped theorem

As the correction warps' `CorrWarp/Src.lean`, with the output warp's positions directly (the
softmax warps make no collective outside the scheduler): a shuffle's source lane is at the same
scan site (`sshfl_recv`), a ballot's bits are the lanes' predicates at the same ballot
(`svote_bits`), the reads return the launch words (the addressed shapes `EvR`), the used-K read
the chosen request's length (`expect_uk`). `sexpect` assembles them; `good` is
`Frame.followedOn` for the lanes of softmax warp `w`, now with the scheduler's reference values in
the invariant. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-! ### The addressed reads at the role's states -/

theorem shapeR (hp : Pre p L m) : (Softmax.code p L g).Shape (EvR p L g) := by
  refine Code.Shape.of_at fun d {t ins e o} hat hi hc hf => ?_
  by_cases hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk
  · have hk : d.k = 0 ∧ d.acc = [] := by
      rcases hi with ⟨h1, h2, -⟩ | hi
      · exact ⟨h1, h2⟩
      · exfalso
        obtain ⟨s, v, k, acc⟩ := d
        rcases hs with ⟨k', h⟩ | h | h | h <;> simp only at h <;> subst h <;>
          simp [Site.midOk] at hi
    rcases hs with ⟨k, h⟩ | h
    · exact shapeR_word hp d hk.1 hk.2 k h hat hi hc hf
    · exact shapeR_req hp d hk.1 hk.2 h hat hi hc hf
  · obtain ⟨s, v, k, acc⟩ := d
    cases s <;> simp_all [EvR]

/-- An event at a role state of a softmax lane has its addressed read shape. -/
theorem fired_r (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {d : Control.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hs : Frame.stateAt (thread p L) X g k = some (some (sinj p L g d n)))
    (hu : ∀ f, e.kind ≠ .ub f) : EvR p L g d.scheduler e := by
  obtain ⟨_, _, _, hat, hi, hc, hf⟩ :=
    Frame.fired_siteU (fun _ hg => thread_sound hp hg) hX he hs hu
  by_cases hb : ∃ b c, d.site = .bld b c
  · obtain ⟨b,c,hs⟩ := hb
    exact (by unfold EvR; rw [show d.scheduler.site = _ from hs]; trivial)
  · apply shapeR (g := g) hp (d := d.scheduler) hat _ hc hf
    obtain ⟨s,v,k,acc⟩ := d
    cases s <;> first | exact hi.1 | exact (hb ⟨_,_,rfl⟩).elim

/-! ### Events at the role's states -/

/-- The induction hypothesis: the lanes of warp `w` are followed at the positions with at most
`n` collectives before them. -/
abbrev GoodUpTo (p : Params) (L : Launch) (w : Nat) (X : Execution) (n : Nat) : Prop :=
  Proof.GoodUpTo (Ref p L w) X w n

/-- The kind of event a softmax site fires, as far as the collectives and the return go. -/
theorem ev_class {d : D} {e : Event} (hev : Softmax.Ev p L g d e) :
    (Execution.isShfl e = true → (epi d.site).shfl = true) ∧
      (isFullVote e = true → ∃ l, d.site = .vote l) ∧
      (e.kind = .exit → ∃ l, epi d.site = .exit l) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [Epilogue.sh, h, ↓reduceIte] at h1; split at h1 <;> simp_all
  · simp only [Epilogue.vt, h, ↓reduceIte] at h2
    split at h2
    · rename_i hb
      obtain ⟨s, v, k, acc⟩ := d
      cases s <;> simp_all [epi, Epilogue.Site.ballot]
    · simp at h2
  · obtain ⟨pc, kind⟩ := e
    simp only at h
    subst h
    obtain ⟨s, v, k, acc⟩ := d
    cases s <;> simp only [Softmax.Ev] at hev
    all_goals (try split at hev)
    all_goals simp_all [epi, Epilogue.Ev, rdOrUb, tcLdOrUb, Site.toE]

/-- A followed state of a softmax lane before an event that is no undefined behaviour. -/
theorem good_cases (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : Good p L w X g j) :
    (∃ s n, Frame.stateAt (thread p L) X g j = some (some (.inl s, n)) ∧
        StartW L w s n ∧ n .vote = 0 ∧ ZeroS n) ∨
      (∃ d n, Frame.stateAt (thread p L) X g j = some (some (sinj p L g d n)) ∧ n .ub = 0 ∧
        3 ≤ n .shfl ∧ SFits p L g d (n .shfl) (n .vote)) := by
  obtain ⟨⟨σ, n⟩, hσ, hR⟩ := good_state hp hX he hub hG
  rcases σ with s | ⟨i, d⟩
  · exact .inl ⟨s, n, hσ, hR⟩
  · cases i with
    | softmax =>
      have h0 := ub_zero hX he hσ
      exact .inr ⟨d, n, hσ, h0, hR.1, (hR.2 h0).2⟩
    | _ => exact hR.elim

/-- A role state of a softmax lane at an event that is a collective past the startup's or a
return: its reference values, its shape and its counts. -/
theorem role_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat} {e :
    Event} (he : X.get (h, j) = some e)
    (hG : Good p L w X h j)
    (hk : (Execution.isShfl e = true ∧ 3 ≤ ((X.tr h).take j).countP Execution.isShfl) ∨
      isFullVote e = true ∨ e.kind = .exit) :
    ∃ d n, Frame.stateAt (thread p L) X h j = some (some (sinj p L h d n)) ∧
      SFits p L h d (n .shfl) (n .vote) ∧ Softmax.Ev p L h d e ∧
      ((X.tr h).take j).countP Execution.isShfl = n .shfl ∧
      ((X.tr h).take j).countP isFullVote = n .vote := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    rcases hk with ⟨h1, -⟩ | h1 | h1 <;> simp [Execution.isShfl, isFullVote, voteClass] at h1
  rcases good_cases hp hX he hub hG with ⟨s, n, hσ, hS, -⟩ | ⟨d, n, hσ, -, -, hF⟩
  · exfalso
    have hE := (start_fired hp hX he hσ).1
    have hc := (counts hσ).1
    unfold StartW at hS
    split at hS
    · obtain ⟨hv, hx, hsh, -⟩ := start0_kind hS hE
      rcases hk with ⟨h1, h2⟩ | h1 | h1
      · have := hsh h1; rw [hc] at h2; omega
      · rw [hv] at h1; cases h1
      · exact hx h1
    · obtain ⟨hv, hx, hsh, -⟩ := start_kind hS hE
      rcases hk with ⟨h1, h2⟩ | h1 | h1
      · have := hsh h1; rw [hc] at h2; omega
      · rw [hv] at h1; cases h1
      · exact hx h1
  · exact ⟨d, n, hσ, hF, (fired_soft hp hX he hσ (fun f h => hub e.pc f (congrArg (Event.mk e.pc)
      h))).1.1, (counts hσ).1, (counts hσ).2⟩

/-- The output warp's shape of a scan shuffle event. -/
theorem ev_toE {d : D} {e : Event} (hs : (epi d.site).shfl = true) (hev : Softmax.Ev p L g d e) :
    Epilogue.Ev p L g (toE d) e := by
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [epi, Epilogue.Site.shfl, Bool.false_eq_true] at hs <;> exact hev

/-- The output warp's site of a scan shuffle determines the softmax site. -/
theorem epi_shfl_inj {s s' : Site} (hs : (epi s).shfl = true) (h : epi s' = epi s) : s' = s := by
  cases s <;> simp [epi, Epilogue.Site.shfl] at hs <;> cases s' <;> simp_all [epi]

/-- **What a lane's shuffle receives**: the value its source lane sends at the same site. -/
theorem sshfl_recv (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {d : Control.D} {pc : Nat}
    {mode : ShflMode} {a recv : Value} {b c : Nat} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (sinj p L g d n)))
    (hF : SFits p L g d (n .shfl) (n .vote)) (IH : GoodUpTo p L w X (n .shfl + n .vote)) :
    ∃ d' nv', Epilogue.Fits p L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1)
        (toE d') (n .shfl) nv' ∧ (toE d').site = (toE d).site ∧
      recv = .bits 32 (Epilogue.opnd L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1)
        (toE d')) := by
  have hsite := (ev_class (fired_soft hp hX he hσ (fun _ h => by cases h)).1.1).1 rfl
  have h3 := Epilogue.fits_three hF.1
  have hsC := (lane_facts hp hg hw
    (Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) b c)).2.2.1
  obtain ⟨j, pc', b', c', r', o', hj, hG, hjs, -⟩ := shfl_src hp hX hg hw he (counts hσ).1 IH
    (fun h j0 e0 ⟨hh, _⟩ hc he0 hv0 hG hs0 hc0 => by
      simp only [Frame.cnt] at hs0 hc0
      obtain ⟨d0, n0, -, hF0, hE0, hs0', hv0'⟩ := role_at hp hX he0 hG (.inr (.inl hv0))
      obtain ⟨l, hl⟩ := (ev_class hE0).2.1 hv0
      have hlv : (toE d0).site = .vote l := by simp [toE, hl, epi]
      have := Epilogue.shfl_lt_vote hF.1 hF0.1 hc.symm hsite hlv (by omega)
      omega)
    (fun h kx pcx _ hc hx hG hsx hvx => by
      simp only [Frame.cnt] at hsx
      obtain ⟨dx, nx, -, hFx, hEx, hsx', -⟩ := role_at hp hX hx hG (.inr (.inr rfl))
      obtain ⟨l, hl⟩ := (ev_class hEx).2.2 rfl
      have hFx' := hFx.1
      simp only [Epilogue.Fits, toE, hl] at hFx'
      have := Epilogue.shfl_lt_exit hF.1 hc.symm hsite hFx'
      omega)
  simp only [Frame.cnt] at hjs
  obtain ⟨d', n', -, hF', hE', hs', -⟩ := role_at hp hX hj hG (.inl ⟨rfl, by omega⟩)
  have hsite' := (ev_class hE').1 rfl
  have hns : n .shfl = n' .shfl := by omega
  have hFE' := hF'.1
  rw [← hns] at hFE'
  have hsame := Epilogue.shfl_same hF.1 hFE' hsC.symm hsite hsite' rfl
  refine ⟨d', _, hFE', hsame, ?_⟩
  exact Epilogue.ev_opnd (ev_toE hsite' hE')

/-- The role's ballot predicate is the output warp's on the launch's CTA index. -/
theorem votePredS_eq (hp : Pre p L m) (hg : g < L.threads) (l : Bool) (c : Epilogue.D)
    (s : Epilogue.Site) : votePredS p L g l c = Epilogue.votePred p L g { c with site := s } := by
  unfold votePredS Epilogue.votePred
  cases l <;> simp only [ctaOf, Softmax.ctaR_eq hp hg, Bool.false_eq_true, ↓reduceIte]

/-- **A ballot's bits are the predicates of all lanes at the same ballot.** -/
theorem svote_bits (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {d : Control.D} {pc : Nat}
    {a : Bool} {bv : BitVec 32} {l : Bool} (hl : d.site = .vote l)
    (he : X.get (g, k) = some ⟨pc, .vote (2 ^ 32 - 1) a bv⟩)
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (sinj p L g d n)))
    (hF : SFits p L g d (n .shfl) (n .vote)) (IH : GoodUpTo p L w X (n .shfl + n .vote)) :
    ∀ i < 32, ∃ di nvi, Epilogue.Fits p L (g - laneOf L g + i) (toE di) (n .shfl) nvi ∧
      (toE di).site = (toE d).site ∧
      bv.getLsbD i = Epilogue.votePred p L (g - laneOf L g + i) (toE di) := by
  have hlv : (toE d).site = .vote l := by simp [toE, Control.D.scheduler, hl, epi]
  intro i hi
  exact vote_src (P := fun h b => ∃ di nvi, Epilogue.Fits p L h (toE di) (n .shfl) nvi ∧
      (toE di).site = (toE d).site ∧ b = Epilogue.votePred p L h (toE di))
    hp hX hg hw he (counts hσ).2 IH
    (fun h j1 e1 ⟨hh, _⟩ hc he1 hs1 hG hv1 hc1 => by
      simp only [Frame.cnt] at hv1 hc1
      obtain ⟨d1, n1, -, hF1, hE1, hs1', hv1'⟩ :=
        role_at hp hX he1 hG (.inl ⟨hs1, by have := Epilogue.fits_three hF.1; omega⟩)
      have := Epilogue.shfl_lt_vote hF1.1 hF.1 hc ((ev_class hE1).1 hs1) hlv (by omega)
      omega)
    (fun h kx pcx ⟨hh, _⟩ hc hx hG hsx hvx => by
      simp only [Frame.cnt] at hsx hvx
      obtain ⟨dx, nx, -, hFx, hEx, -, hvx'⟩ := role_at hp hX hx hG (.inr (.inr rfl))
      obtain ⟨lx, hlx⟩ := (ev_class hEx).2.2 rfl
      have hFx' := hFx.1
      simp only [Epilogue.Fits, toE, hlx] at hFx'
      exact Epilogue.vote_exit hF.1 hc.symm hlv hFx' (by omega))
    (fun h j ej ⟨hh, _⟩ hc hej hfv hG hsj hcnt => by
      simp only [Frame.cnt] at hsj hcnt
      obtain ⟨di, ni, -, hFi, hEi, -, hvi⟩ := role_at hp hX hej hG (.inr (.inl hfv))
      obtain ⟨li, hli⟩ := (ev_class hEi).2.1 hfv
      have hliv : (toE di).site = .vote li := by simp [toE, hli, epi]
      obtain ⟨hsite, hns⟩ := Epilogue.vote_same hF.1 hFi.1 hc.symm hlv hliv (by omega)
      have hFEi := hFi.1
      rw [hns] at hFEi
      obtain ⟨pcj, kj⟩ := ej
      obtain ⟨si, vi, ki, acci⟩ := di
      change si = .vote li at hli
      subst hli
      have hEi' := hEi
      simp only [Softmax.Ev] at hEi'
      obtain ⟨bj, hkj⟩ := hEi'
      subst hkj
      exact ⟨pcj, _, bj, rfl, _, _, hFEi, hsite, votePredS_eq hp hh _ _ _⟩)
    i hi

/-! ### What the events return -/

/-- **The used-K read returns the chosen request's launch word.** -/
theorem expect_uk (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : D} {ns nv : Nat} {e : Event} (he : X.get (g, k) = some e) (hs : d.site = .uk)
    (hF : SFits p L g d ns nv) (hev : EvR p L g d e) : SExpect p L g d ns e := by
  have hb := Epilogue.batch_lt hp
  have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
    hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  obtain ⟨hFE, -⟩ := hF
  simp only [Epilogue.Fits, toE, hs, epi] at hFE
  obtain ⟨R, bal, hC, -, -⟩ := hFE
  obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
  obtain ⟨pc, kind⟩ := e
  simp only [EvR, hs] at hev
  have hc : chosen d.v.sc = W i := by simpa only [toE] using hi
  rcases hev with ⟨bs, rfl⟩ | ⟨f, rfl⟩
  swap
  · simp [SExpect, hs, Site.sched]
  simp only [SExpect, hs]
  have haddr : (ukAddr p d).toNat = p.usedKBase + 4 * i := by
    rw [ukAddr, hc]
    exact PTX.Kernels.TmlFa4Fwd.Proof.Mma.addrK_toNat hp hroom (by omega)
  rw [haddr] at he
  have hin : ∀ j < 4, ∃ r ∈ p.inputRegions,
      r.Contains ((globalLoc (p.usedKBase + 4 * i)).at j) := by
    intro j hj
    refine ⟨⟨p.usedKBase, 4 * p.batch⟩, by simp [Params.inputRegions], ?_⟩
    simp only [Region.Contains, globalLoc, Loc.at, true_and]
    omega
  rw [inputReadValue hp hX (i := (g, k)) ⟨pc, he⟩ rfl hin (hp.usedK i (by omega)),
    show Value.bits 32 (BitVec.ofNat 64 (p.kLength i)) = b32 (p.kLength i) from rfl, rebuild_b32]
  simp only [b32, ukv, hc, r32_W (show i < 2 ^ 32 by omega),
    toNat_W (show i < 2 ^ 64 by omega)]

set_option maxHeartbeats 4000000 in
/-- **What a softmax lane's scheduler event returns is what the references say.** -/
theorem sexpect (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {d : Control.D} {n : Cls → Nat}
    {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (sinj p L g d n)))
    (hF : SFits p L g d (n .shfl) (n .vote))
    (hne : ∀ f, e.kind ≠ .ub f) (IH : isColl e = true → GoodUpTo p L w X (n .shfl + n .vote)) :
    SExpect p L g d (n .shfl) e := by
  have hev := (fired_soft hp hX he hσ hne).1.1
  have hevR := fired_r hp hX he hσ hne
  by_cases hu : d.site = .uk
  · exact expect_uk hp hX he hu hF hevR
  obtain ⟨hFE, huk⟩ := hF
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case word k' =>
    simp only [SExpect]; intro _
    exact Epilogue.expect_word hp hReads he rfl hFE hevR
  case q0 =>
    simp only [SExpect]; intro _
    exact Epilogue.expect_q hp hReads he (.inl rfl) hFE hevR
  case q1 =>
    simp only [SExpect]; intro _
    exact Epilogue.expect_q hp hReads he (.inr rfl) hFE hevR
  case down | up | total | pre | tiles =>
    simp only [SExpect]; intro _
    have hevE := ev_toE (by rfl) hev
    have hk : ∃ md a b c r ok, kind = .shfl md a b c r ok := by
      simp only [Softmax.Ev] at hev
      revert hev; simp only [Epilogue.Ev, Site.toE]
      first
        | (rintro ⟨r, ok, h⟩; exact ⟨_, _, _, _, _, _, h⟩)
    obtain ⟨md, a, b, c, r, ok, rfl⟩ := hk
    obtain ⟨d', nv', h1, h2, h3⟩ := sshfl_recv hp hX hg hw he hσ ⟨hFE, huk⟩ (IH rfl)
    exact Epilogue.expect_shfl_of_src hp hg hw hevE ⟨toE d', nv', h1, h2, h3⟩
  case vote l =>
    simp only [SExpect]; intro _
    have hk : ∃ a b, kind = .vote (2 ^ 32 - 1) a b := by
      simp only [Softmax.Ev] at hev; obtain ⟨b, h⟩ := hev; exact ⟨_, _, h⟩
    obtain ⟨a, b, rfl⟩ := hk
    have hb := svote_bits hp hX hg hw rfl he hσ ⟨hFE, huk⟩ (IH isColl_vote)
    exact Epilogue.expect_vote_of_bits hp hg hw (l := l) rfl fun i hi => by
      obtain ⟨di, nvi, h1, h2, h3⟩ := hb i hi
      exact ⟨toE di, nvi, h1, h2, h3⟩
  case bar1 =>
    simp only [SExpect]; intro _
    simp only [Epilogue.Expect, toE, Control.D.scheduler, epi]
  case uk => exact absurd rfl hu
  all_goals exact fun h => by cases h

set_option maxHeartbeats 1000000 in
/-- **Every event of a lane of softmax warp `w` at a state that holds `Ref` makes a good
step.** -/
theorem step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hw8 : w < 8)
    (g k : Nat) (σ : (thread p L g).D) (e : Event)
    (hQ : InWarp L w g) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hR : Ref p L w g σ)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L w) X j) :
    Frame.StepGood (thread p L) (Ref p L w) g σ e := by
  obtain ⟨hg, hw⟩ := hQ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · exact start_step hp hX hg hw hw8 he hσ hR hprev
  · cases i with
    | softmax =>
      have hF := (hR.2 (ub_zero hX he hσ)).2
      obtain ⟨hcs, hcv⟩ := counts hσ
      apply role_step hp hX he hσ hR
      intro hne
      have hSE := sexpect hp hX (cuQReadsFromLaunch hp hX) hg hw he hσ hF hne fun hce => by
        have := upTo_of_prev (fun _ => ref_init) he hce hprev
        rwa [countColl ((X.tr g).take k), hcs, hcv] at this
      refine ⟨?_, hSE⟩
      obtain ⟨s,v,k,acc⟩ := d
      cases s with
      | bld | sld => trivial
      | _ => exact expectD_of hp hg hF hSE trivial
    | _ => exact hR.elim

/-- **Every lane of softmax warp `w` is followed, and its states hold the reference
invariant**, given the numeric steps, the data stores' safety and the sources. -/
theorem good (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hw8 : w < 8) (hg : g
    < L.threads)
    (hw : Prologue.warpIndex L g = w) (k : Nat) : Good p L w X g k :=
  Frame.followedOn (C := thread p L) (J := Ref p L w) (Q := InWarp L w)
    (Frame.inductive_lex (μ X)) (fun _ _ => ref_init)
    (step hp hX hw8) ⟨hg, hw⟩ k

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
