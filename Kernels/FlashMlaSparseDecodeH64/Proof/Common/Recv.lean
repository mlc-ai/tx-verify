-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
public import Lemmas.Kernel.Source.WarpColl
public import Lemmas.Kernel.FrameU
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.RefNext
import Lemmas.Flow.WarpScan

@[expose] public section

/-! # The startup's shuffles return the launch's words, and the dispatch's gates pass

The words the startup records (`Startup.RefW`) and the warp the head's exits pass on
(`Wg1.HRef`) are part of the role table's invariant, so the following premise owes them. This
file gives what discharges them and what they give:

* `startup_recv`: **the source fact**. A startup shuffle (the thread's first or second) returns
  the word lane 0 of its warp sent: the launch's warpgroup word (`wgW`), then its warp word
  (`warpW`). The lanes of the warp are followed at every position with at most the collectives
  before the shuffle (`Frame.GoodUpTo`, from the following induction's earlier events by
  `Frame.upTo_of_lt`, or from `Follow` itself); at such a position a lane has made at most one
  shuffle, so it is at a startup shuffle (`early`), and lane 0 at the shuffle of the same
  instance sent its word.
* `sel_pass`, `subSel_pass`: **the gates pass** at a state with the invariant: the startup's
  exit records the launch's words, the head's exit is the launch's warp's. So a followed thread
  never enters a stub.
* `head_recv`: the same for the head's shuffle (pc 1843, the thread's third): it returns the
  launch's warp word (`warpW`); `head_refNext` discharges `Wg1.hrefNext`'s shuffle premise.
* `startup_recv_follow`: the source fact under `Follow`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- At a followed position of a lane with at most one shuffle before it, the event (no undefined
behaviour) is fired from the startup's shuffle of that count. -/
private theorem early (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j : Nat} {e : Event} (hj : X.get (h, j) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) (hG : Frame.FollowedAt (thread P L) (table P L).J X h j)
    (hc : Frame.cnt X Execution.isShfl h j ≤ 1) :
    ∃ s : Startup.D, ∃ jj : Fin 2, s.site = .sh jj ∧
      Frame.cnt X Execution.isShfl h j = jj.val ∧ Startup.Ev L h s e := by
  have hC : ∀ g < L.threads, (thread P L g).SoundU := fun g _ => thread_sound hp
  obtain ⟨σ, hσ, hJ⟩ := Frame.good_stateU hC hX hj (fun pc f hk => hu f (by rw [hk])) hG
  obtain ⟨t, ins, o, hat, hi, hcode, hf⟩ := Frame.fired_siteU hC hX hj hσ hu
  have hev := (shapeOk hp (fun _ => True)).shape h trivial σ t ins e o hJ hat hi hcode hf
  have hn := state_count hσ .shfl
  obtain ⟨s, n⟩ := σ
  simp only [cls] at hn
  rcases s with d | ⟨i | r, d'⟩
  · obtain ⟨-, hW, -⟩ := hJ
    obtain ⟨site, x1, x2⟩ := d
    cases site with
    | sh jj =>
      obtain ⟨h2, -⟩ := hW
      exact ⟨⟨.sh jj, x1, x2⟩, jj, rfl, by simp only [Frame.cnt]; omega, hev⟩
    | bar => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | enter q => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | elect _ => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | init _ => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | fence => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | alloc => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | allocSt => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | ld => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | trap => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
    | relinq => obtain ⟨h2, -⟩ := hW; simp only [Frame.cnt] at hc; omega
  · exfalso
    have h2 : 2 ≤ n .shfl := by
      cases i
      · obtain ⟨-, -, h2, -⟩ := hJ; exact h2
      · obtain ⟨-, -, h2, -⟩ := hJ; exact h2
      · obtain ⟨-, -, h2, -⟩ := hJ; exact h2
    simp only [Frame.cnt] at hc
    omega
  · exact hJ.elim

/-- A startup shuffle site fires a shuffle. -/
private theorem sh_kind {s : Startup.D} {jj : Fin 2} {e : Event} (hs : s.site = .sh jj)
    (hev : Startup.Ev L g s e) :
    ∃ r ok, e.kind = .shfl .idx (w32 (if jj.val = 0 then BitVec.ofNat 64 (tidOf L g / 128)
      else Arith32.shru (tw L g) 5)) 0 31 r ok := by
  obtain ⟨site, x1, x2⟩ := s
  simp only at hs
  subst hs
  fin_cases jj
  · exact hev
  · exact hev

/-- **The source fact of the startup's shuffles**: the thread's shuffle with `jj` shuffles before
it returns the launch's warpgroup word (`jj = 0`) or warp word (`jj = 1`), when the lanes of its
warp are followed at the positions with at most the collectives before it. -/
theorem startup_recv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {a r : Value} {ok : Bool} {jj : Fin 2}
    (he : X.get (g, k) = some ⟨pc, .shfl .idx a 0 31 r ok⟩)
    (hc : Frame.cnt X Execution.isShfl g k = jj.val)
    (IH : Frame.GoodUpTo (thread P L) (table P L).J X (g % L.block / 32)
      (((X.tr g).take k).countP Frame.isColl)) :
    r = w32 (if jj.val = 0 then wgW L g else warpW L g) := by
  have hg := Frame.lt_of_get hX he
  have hb : L.block % 32 = 0 := by rw [hp.block]
  have hj1 := jj.isLt
  rw [Frame.countColl] at IH
  simp only [Frame.cnt] at hc
  rw [hc] at IH
  obtain ⟨j, pc', b', c', r', o', hsj, hG, hcs, -⟩ := Frame.shfl_src hb hX hg rfl he hc IH
    (fun h j e _ _ hj hv hG hcs _ => by
      obtain ⟨s, jj', hs, -, hev⟩ := early hp hX hj
        (fun f hk => by simp [voteWith, voteClass, hk] at hv) hG (by omega)
      obtain ⟨r0, ok0, hk⟩ := sh_kind hs hev
      simp [voteWith, voteClass, hk] at hv)
    (fun h j pc _ _ hj hG hcs _ => by
      obtain ⟨s, jj', hs, -, hev⟩ := early hp hX hj (fun f hk => by cases hk) hG
        (by omega)
      obtain ⟨r0, ok0, hk⟩ := sh_kind hs hev
      cases hk)
  obtain ⟨s, jj', hs, hc', hev⟩ := early hp hX hsj (fun f hk => by cases hk) hG
    (by omega)
  have hjj : jj' = jj := Fin.ext (by omega)
  obtain ⟨r0, ok0, hk⟩ := sh_kind hs hev
  rw [hjj] at hk
  simp only [Kind.shfl.injEq] at hk
  obtain ⟨-, hr, -⟩ := hk
  rw [hr, shflSource_idx _ (by decide)]
  fin_cases jj
  · simp only [↓reduceIte]
    show _ = w32 (BitVec.ofNat 64 (wgOf L g))
    rw [← lane0_wg hp g]
    rfl
  · simp only [one_ne_zero, ↓reduceIte]
    show w32 (Arith32.shru (BitVec.ofNat 64 (tidOf L _)) 5) = _
    rw [shru_tw hp]
    simp only [warpW, lane0_warp hp g]

/-- At a followed position of a warpgroup-1 lane with at most two shuffles before it, the event
(no undefined behaviour) is no vote and no `exit`, and a shuffle after two is the head's, which
sends the lane's warp index. -/
private theorem early_head (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j : Nat} {e : Event} (hj : X.get (h, j) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) (hG : Frame.FollowedAt (thread P L) (table P L).J X h j)
    (hc : Frame.cnt X Execution.isShfl h j ≤ 2) (hwg : wgOf L h = 1) :
    voteClass e.kind = none ∧ e.kind ≠ .exit ∧
      (Frame.cnt X Execution.isShfl h j = 2 → ∀ md a b c r ok,
        e.kind = .shfl md a b c r ok → a = w32 (Arith32.shru (tw L h) 5)) := by
  have hC : ∀ g < L.threads, (thread P L g).SoundU := fun g _ => thread_sound hp
  obtain ⟨σ, hσ, hJ⟩ := Frame.good_stateU hC hX hj (fun pc f hk => hu f (by rw [hk])) hG
  obtain ⟨t, ins, o, hat, hi, hcode, hf⟩ := Frame.fired_siteU hC hX hj hσ hu
  have hev := (shapeOk hp (fun _ => True)).shape h trivial σ t ins e o hJ hat hi hcode hf
  have hn := state_count hσ .shfl
  obtain ⟨s, n⟩ := σ
  simp only [cls] at hn
  simp only [Frame.cnt] at hc ⊢
  rw [← hn] at hc ⊢
  rcases s with d | ⟨i | r, d'⟩
  · have hx : Startup.exitOf d = none := by
      have := hi.2
      simpa [Code.gatedExit, startupEnter] using this
    obtain ⟨hv, hsh⟩ := Startup.ev_coll hev hx
    obtain ⟨-, hex, -⟩ := Startup.ev_quiet hev hx
    refine ⟨hv, hex, fun h2 md a b c r ok hk => ?_⟩
    obtain ⟨jj, hs⟩ := hsh md a b c r ok hk
    obtain ⟨-, hW, -⟩ := hJ
    obtain ⟨site, x1, x2⟩ := d
    simp only at hs
    subst hs
    obtain ⟨hcnt, -⟩ := hW
    have := jj.isLt
    omega
  · cases i with
    | wg0 => obtain ⟨-, -, -, hg⟩ := hJ; simp [Entry.wg, hwg] at hg
    | dequant => obtain ⟨-, -, -, hg⟩ := hJ; simp [Entry.wg, hwg] at hg
    | wg1 =>
      obtain ⟨-, hW, -, -⟩ := hJ
      rcases d' with s | ⟨jj | r, d⟩
      · have hx := hi.2
        cases s with
        | smr =>
          obtain ⟨inst, hk⟩ := hev
          exact ⟨by simp [hk, voteClass], by simp [hk], fun _ md a b c r ok h => by
            rw [hk] at h; cases h⟩
        | hsh =>
          obtain ⟨r, ok, hk⟩ := hev
          refine ⟨by simp [hk, voteClass], by simp [hk], fun _ md a b c r' ok' h => ?_⟩
          rw [hk] at h
          cases h
          rfl
        | _ => simp [Code.gatedExit, wg1Enter, Wg1.exitOf] at hx
      · have h3 : 3 ≤ n .shfl := by cases jj <;> exact hW.1
        omega
      · exact hW.elim
  · exact hJ.elim

/-- **The source fact of the head's shuffle**: a warpgroup-1 lane's shuffle after the startup's
two (pc 1843) returns the launch's warp word, when the lanes of its warp are followed at the
positions with at most the collectives before it. -/
theorem head_recv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {a r : Value} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl .idx a 0 31 r ok⟩)
    (hc : Frame.cnt X Execution.isShfl g k = 2) (hwg : wgOf L g = 1)
    (IH : Frame.GoodUpTo (thread P L) (table P L).J X (g % L.block / 32)
      (((X.tr g).take k).countP Frame.isColl)) :
    r = w32 (warpW L g) := by
  have hg := Frame.lt_of_get hX he
  have hb : L.block % 32 = 0 := by rw [hp.block]
  have hsame : ∀ h, h % L.block / 32 = g % L.block / 32 → wgOf L h = 1 := by
    intro h hh
    simp only [wgOf, tidOf_eq hp] at hwg ⊢
    rw [hp.block] at hh
    omega
  rw [Frame.countColl] at IH
  simp only [Frame.cnt] at hc
  rw [hc] at IH
  obtain ⟨j, pc', b', c', r', o', hsj, hG, hcs, -⟩ := Frame.shfl_src hb hX hg rfl he hc IH
    (fun h j e hw _ hj hv hG hcs _ => by
      obtain ⟨hv', -, -⟩ := early_head hp hX hj
        (fun f hk => by simp [voteWith, voteClass, hk] at hv) hG hcs (hsame h hw.2)
      simp [voteWith, hv'] at hv)
    (fun h j pc hw _ hj hG hcs _ => by
      obtain ⟨-, hex, -⟩ := early_head hp hX hj (fun f hk => by cases hk) hG hcs
        (hsame h hw.2)
      exact hex rfl)
  obtain ⟨-, -, hsrc⟩ := early_head hp hX hsj (fun f hk => by cases hk) hG (by omega)
    (hsame _ (by
      obtain ⟨-, hw, -⟩ := Frame.lane_facts hb hg rfl
        (Step.shflSource_lt .idx (show PTX.laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31)
      exact hw))
  have ha := hsrc hcs _ _ _ _ _ _ rfl
  rw [ha, shflSource_idx _ (by decide)]
  show w32 (Arith32.shru (BitVec.ofNat 64 (tidOf L _)) 5) = _
  rw [shru_tw hp]
  simp only [warpW, lane0_warp hp g]

/-- **The startup's gate passes** at an exit state with the invariant. -/
theorem sel_pass {d : Startup.D} {n : Cls → Nat} {r : Entry} (hJ : startupJ P L g d n)
    (hx : startupEnter P L g d = some r) : sel P L g r d = some r := by
  obtain ⟨-, hW, -⟩ := hJ
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | enter q =>
    obtain ⟨-, h1, h2⟩ := hW
    exact ite_eq_left_of_eq_true _ _ (eq_true (show x1 = wgW L g ∧ x2 = warpW L g from ⟨h1, h2⟩))
  | _ => simp [startupEnter, Startup.exitOf] at hx

/-- **Warpgroup 1's gates pass** at a head exit with the invariant. -/
theorem subSel_pass {s : Wg1.Site} {sh : Nat} {r : SubEntry} (hJ : Wg1.HRef L g s sh)
    (hx : wg1Enter P L g s = some r) : subSel P L g r s = some r := by
  cases s <;> simp only [wg1Enter, Wg1.exitOf, Option.map_some, Option.map_none,
    Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;> simp only [Wg1.HRef] at hJ
  · obtain ⟨-, hw⟩ := hJ
    simp [subSel, subOk, hw]
  · obtain ⟨-, hw⟩ := hJ
    simp [subSel, subOk, hw]
  · obtain ⟨-, hw⟩ := hJ
    simp only [subSel, subOk, hw, beq_self_eq_true, ↓reduceIte]
  · obtain ⟨-, h4, h7⟩ := hJ
    simp [subSel, subOk, h4, h7]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
