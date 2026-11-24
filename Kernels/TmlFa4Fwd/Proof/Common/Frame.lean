-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Lemmas.Flow.Arith32Word
public import Lemmas.Kernel.Followed
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Lemmas.Kernel.FrameU
import Lemmas.Flow.WarpScan
import Lemmas.Kernel.Counted
import Lemmas.Kernel.Source.WarpColl
import Lemmas.Kernel.UbLast
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The thread frame and the startup of a lane of any warp

Facts about `Frame.stateAt (thread p L)` that do not depend on the role a thread enters.

* **Counts.** The ghost counts of a state are the thread's events of each class before it
  (`count`); the count of all events is the position (`count_all`). A state before an event has
  seen no undefined behaviour (`ub_zero`): an undefined-behaviour event is its thread's last.
* **Order.** The warp collectives are the shuffles and full-mask ballots (`isColl`); the order of
  the never-dropped induction is by the collectives up to and including an event (`μ`), and the
  source lanes of a collective are followed up to it (`upTo_of_prev`).
* **Startup.** A lane of warp `w` passes the startup's three shuffles, the fence and the barrier
  (`StartAt L w`), with the shared base and the warp index `w` as the shuffled words. Its
  shuffles' values come from lane 0 of the warp (`start_recv`), and every startup step keeps
  `StartAt` until the barrier (`start_next`). These facts hold for the lanes of every warp that
  takes the fence path (warp index not 0); the roles' reference invariants add their own counts. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Counts -/

/-- **The counts of a state are the thread's events of each class before it.** -/
theorem count {k : Nat} {σ : (glued p L g).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (σ, n))) (c : Cls) :
    ((X.tr g).take k).countP (cls L g c) = n c :=
  (Frame.count_eq (C := glued p L) (cls := fun g => cls L g) hσ c).symm

theorem counts {k : Nat} {σ : (glued p L g).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (σ, n))) :
    ((X.tr g).take k).countP Execution.isShfl = n .shfl ∧
      ((X.tr g).take k).countP isFullVote = n .vote :=
  ⟨count hσ .shfl, count hσ .vote⟩

/-- The count of all events before a state within the trace is its position. -/
theorem count_all {k : Nat} {σ : (glued p L g).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (σ, n))) (hk : k ≤ (X.tr g).length) :
    n .all = k := by
  rw [← count hσ .all]
  simp [cls, List.countP_true, List.length_take, Nat.min_eq_left hk]

/-- An event of a class the state has counted is an earlier event of the thread. -/
theorem exists_of_count {k : Nat} {σ : (glued p L g).D} {n : Cls → Nat} {c : Cls}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (σ, n))) (h : 0 < n c) :
    ∃ j < k, ∃ f, X.get (g, j) = some f ∧ cls L g c f = true :=
  Frame.exists_of_count (C := glued p L) (cls := fun g => cls L g) hσ h

/-- **A state before an event has seen no undefined behaviour.** -/
theorem ub_zero (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {e : Event}
    {σ : (glued p L g).D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (σ, n))) : n .ub = 0 := by
  by_contra h
  obtain ⟨j, hj, ⟨pc, kind⟩, hf, hc⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
  cases kind <;> simp [cls] at hc
  have := ub_last hX (show X.get (g, j) = some ⟨pc, .ub _⟩ from hf) he
  omega

/-- **An event at a startup state has the startup's site shape**, and the state is no exit. -/
theorem start_fired (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {s : Startup.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) :
    Startup.Ev L g s e ∧ exit L g s = none ∧ e.pc = s.site.pc := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf0⟩ := strict_fired hp hX he hσ rfl
  have hpc := Code.fired_pc (C := glued p L g) (Code.counted_fired.mp hf0)
  obtain ⟨t, ⟨hat, hi, hx⟩, hf⟩ := hf0
  obtain ⟨ins, hc, -, -⟩ := (startup_steps hp hg s hx).site hi
  change Fires t.pc (match kernel.code[(Startup.code p L g).pc s]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e o at hf
  rw [hc, hat.1] at hf
  exact ⟨Startup.shape hp hat hi hc hf, hx, hpc⟩

/-- A followed state before an event that is no undefined behaviour is a state that holds the
reference invariant. -/
theorem good_state {J : (g : Nat) → (thread p L g).D → Prop} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : Frame.FollowedAt (thread p L) J X g j) :
    ∃ σ, Frame.stateAt (thread p L) X g j = some (some σ) ∧ J g σ :=
  Frame.good_stateU (fun _ hg => thread_sound hp hg) hX he hub hG

/-! ### The order by the warp collectives -/

/-- The warp collectives: shuffles and full-mask ballots. -/
def isColl (e : Event) : Bool := Execution.isShfl e || isFullVote e

/-- The warp collectives up to and including an event: the order of the induction. -/
def μ (X : Execution) (i : EvId) : Nat := ((X.tr i.1).take (i.2 + 1)).countP isColl

theorem isShfl_not_vote {e : Event} (h : Execution.isShfl e = true) : isFullVote e = false :=
  Frame.isShfl_not_vote h

theorem countColl (es : List Event) :
    es.countP isColl = es.countP Execution.isShfl + es.countP isFullVote :=
  Frame.countColl es

/-- The lanes of warp `w`. -/
def InWarp (L : Launch) (w g : Nat) : Prop := g < L.threads ∧ Prologue.warpIndex L g = w

/-- The lanes of the warp of a lane of warp `w`. -/
theorem lane_facts {w : Nat} (hp : Pre p L m) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) {i : Nat} (hi : i < 32) :
    let h := g - laneOf L g + i
    h < L.threads ∧ Prologue.warpIndex L h = w ∧ h / L.block = g / L.block ∧
      laneOf L h = i ∧ SameWarp L g h :=
  Frame.lane_facts (by rw [hp.block]) hg hw hi

/-- The lanes of warp `w` are followed with `J` at the positions with at most `n` collectives
before them. -/
def GoodUpTo (J : (g : Nat) → (thread p L g).D → Prop) (X : Execution) (w n : Nat) : Prop :=
  ∀ h j, InWarp L w h → ((X.tr h).take j).countP isColl ≤ n → Frame.FollowedAt (thread p L) J X h j

/-- **The source lanes of a collective are followed up to it**: with the order by the
collectives, every position of a lane of warp `w` with at most the collectives before the event
is followed. Only the lanes' events with fewer collectives up to them than the event are used. -/
theorem upTo_of_lt {J : (g : Nat) → (thread p L g).D → Prop} {w k : Nat} {e : Event}
    (hinit : ∀ g, J g (thread p L g).init) (he : X.get (g, k) = some e) (hc : isColl e = true)
    (hprev : ∀ j, μ X j < μ X (g, k) → InWarp L w j.1 → ¬ Frame.Bad (thread p L) J X j) :
    GoodUpTo J X w (((X.tr g).take k).countP isColl) :=
  Frame.upTo_of_lt (C := thread p L) hinit he hc hprev

theorem upTo_of_prev {J : (g : Nat) → (thread p L g).D → Prop} {w k : Nat} {e : Event}
    (hinit : ∀ g, J g (thread p L g).init) (he : X.get (g, k) = some e) (hc : isColl e = true)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) J X j) :
    GoodUpTo J X w (((X.tr g).take k).countP isColl) :=
  upTo_of_lt hinit he hc fun j hj => hprev j (.inl hj)

/-! ### The startup of a lane of warp `w` -/

/-- The startup's words and counts on a lane of warp `w`: the shuffles so far returned the
shared base and the warp index `w`, and the dispatch goes to the fence and the barrier. -/
def StartAt (L : Launch) (w : Nat) (s : Startup.D) (n : Cls → Nat) : Prop :=
  match s.site with
  | .sh j => n .shfl = j.val ∧ n .all = j.val ∧
      (0 < j.val → s.x1 = BitVec.ofNat 64 L.sharedBase) ∧ (j.val = 2 → s.x2 = BitVec.ofNat 64 w)
  | .fence => n .shfl = 3 ∧ n .all = 3 ∧ s.x1 = BitVec.ofNat 64 L.sharedBase ∧
      s.x3 = BitVec.ofNat 64 w
  | .bar => n .shfl = 3 ∧ n .all = 4 ∧ s.x1 = BitVec.ofNat 64 L.sharedBase ∧
      s.x3 = BitVec.ofNat 64 w
  | _ => False

theorem startAt_le {w : Nat} {s : Startup.D} {n : Cls → Nat} (h : StartAt L w s n) :
    n .all ≤ 4 ∧ n .shfl ≤ 3 ∧ (n .shfl < 3 → n .all = n .shfl) := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp only [StartAt] at h <;> omega

/-- The classes a startup event of the fence path counts: shuffles, all events, and the barrier
among the MMA warp's named-barrier arrivals. -/
def StartCls (c : Cls) : Prop := c = .shfl ∨ c = .all ∨ c = .mma .bar

open PTX.Flow.Arith32 in
/-- The correction warps' named barriers are not the CTA barrier 0 of the startup. -/
theorem corr_nb_ne (k : Fin 2) : (Correction.nbOf L g k).toNat ≠ 0 := by
  have key : ∀ (x : BitVec 64) (n : Nat), 1 ≤ n → n ≤ 7 → (addi (andi x 3) n).toNat ≠ 0 := by
    intro x n h1 hn
    have h := (show (andi x 3).toNat ≤ 3 from by
      simp only [andi, r32, i32, BitVec.toNat_and]; exact (Nat.and_le_right).trans (by decide))
    simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
      BitVec.toNat_ofInt]
    generalize (andi x 3).toNat = a at h ⊢
    have : ((n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = n := by omega
    rw [this]
    omega
  fin_cases k
  · exact key _ 3 (by decide) (by decide)
  · exact key _ 7 (by decide) (by decide)

theorem corr_nb_ne' (k : Fin 2) : 0 ≠ (Correction.nbOf L g k).toNat := (corr_nb_ne k).symm

theorem soft_nbW_word8 : ∀ w < 8,
    (Epilogue.addi (Epilogue.add32 (Epilogue.sub32 (BitVec.ofNat 64 w)
      (Epilogue.andi (Epilogue.add32 (BitVec.ofNat 64 w)
        (Epilogue.shru (Epilogue.shrs (BitVec.ofNat 64 w) 31) 30)) (-4)))
      (Epilogue.sel (Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3) (Epilogue.i32 4)
        (Epilogue.i32 0))) 3).toNat ≠ 0 := by
  decide

/-- A softmax lane's named barrier with the correction warps is not the CTA barrier 0. -/
theorem soft_nb_ne' (h : g % L.block / 32 < 8) : 0 ≠ (Softmax.nbW L g).toNat :=
  (soft_nbW_word8 _ h).symm

/-- **The startup's events on a lane of warp `w`**: shuffles before the third, the fence and the
barrier; none is a ballot, a return, undefined behaviour or of a class a role counts. -/
theorem start_kind {w : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartAt L w s n)
    (hE : Startup.Ev L g s e) :
    isFullVote e = false ∧ e.kind ≠ .exit ∧ (Execution.isShfl e = true → n .shfl < 3) ∧
      s.site.pc ≤ 173 ∧ ∀ c, cls L g c e = true → StartCls c := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  have hc : ∀ k : Kind, (k = .fenceMbarInit ∨ k = .bar 0 none .sync ∨
      ∃ a b c r o, k = .shfl .idx a b c r o) → isFullVote ⟨pc, k⟩ = false ∧ k ≠ .exit ∧
      ∀ c, cls L g c ⟨pc, k⟩ = true → StartCls c := by
    rintro k (rfl | rfl | ⟨a, b, c, r, o, rfl⟩) <;>
      refine ⟨rfl, by simp, fun c h => ?_⟩ <;> unfold StartCls <;> cases c <;>
      try simp_all [cls, Epilogue.isStore, Epilogue.isCommit, Epilogue.isWait,
        Epilogue.isArrive, sourceWaitSuccess, sourceArrive, isFullVote, voteClass]
    all_goals (rename_i c; cases c <;>
      simp_all [Mma.cls, Correction.cls, Loader.cls, corr_nb_ne', Softmax.cls,
        Softmax.Cnt.pointed])
    all_goals first
      | exact absurd h.1 (soft_nb_ne' h.2)
      | (obtain ⟨h1, -⟩ := h; split at h1 <;> omega)
  cases site <;> simp only [StartAt] at hS
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hE <;> obtain ⟨r, o, rfl⟩ := hE <;>
      obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inr ⟨_, _, _, _, _, rfl⟩)) <;>
      exact ⟨h1, h2, fun _ => by simp_all, by simp [Startup.Site.pc], h3⟩
  case fence =>
    simp only [Startup.Ev] at hE
    obtain ⟨h1, h2, h3⟩ := hc _ (.inl hE)
    exact ⟨h1, h2, fun h => by simp [Execution.isShfl, hE] at h, by simp [Startup.Site.pc], h3⟩
  case bar =>
    simp only [Startup.Ev] at hE
    obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inl hE))
    exact ⟨h1, h2, fun h => by simp [Execution.isShfl, hE] at h, by simp [Startup.Site.pc], h3⟩

/-- A startup state before the third shuffle is at the shuffle of its count. -/
theorem startAt_site {w : Nat} {s : Startup.D} {n : Cls → Nat} (h : StartAt L w s n) {j : Fin 3}
    (hj : n .shfl = j.val) : s.site = .sh j := by
  obtain ⟨site, x1, x2, x3⟩ := s
  have := j.isLt
  cases site <;> simp only [StartAt] at h <;> try omega
  case sh j' => exact congrArg _ (Fin.ext (h.1.symm.trans hj))

/-- **What a startup shuffle of a lane of warp `w` sends**: the shared base, then the warp index
twice. -/
theorem start_sent {w : Nat} (hp : Pre p L m) (hw : Prologue.warpIndex L g = w) {s : Startup.D}
    {n : Cls → Nat} {e : Event} {j : Fin 3} (hS : StartAt L w s n) (hs : s.site = .sh j)
    (hE : Startup.Ev L g s e) :
    ∃ r ok, e.kind = .shfl .idx (b32 (if j.val = 0 then L.sharedBase else w)) 0 31 r ok := by
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at hs
  subst hs
  simp only [StartAt] at hS
  fin_cases j <;> simp only [Startup.Ev] at hE <;> obtain ⟨r, ok, hk⟩ := hE <;>
    refine ⟨r, ok, hk.trans ?_⟩ <;> simp only at hS ⊢
  · rfl
  · rw [Startup.warpW_eq hp, show g % L.block / 32 = w from hw]; rfl
  · rw [hS.2.2.2 trivial]; rfl

/-- **What a startup shuffle of a lane of warp `w` returns**: the shared base from lane 0, then
the warp index twice. The reference invariant `J` of the warp's lanes gives a startup invariant
`S` and no ballot at a startup state, and at least the startup's three shuffles at a role state;
`S` fires no ballot and no return, and is `StartAt` before the third shuffle (`StartAt` itself
for the warps that take the fence path, `StartAt0` for warp 0). Only the lanes' events with
fewer collectives up to them are used (`hprev`). -/
theorem start_recv_of {J : (g : Nat) → (thread p L g).D → Prop} {w : Nat}
    {S : Startup.D → (Cls → Nat) → Prop}
    (hSk : ∀ h s n e, S s n → Startup.Ev L h s e → isFullVote e = false ∧ e.kind ≠ .exit)
    (hSsh : ∀ s n, S s n → n .shfl < 3 → StartAt L w s n)
    (hinit : ∀ g, J g (thread p L g).init)
    (hJs : ∀ h s n, J h (.inl s, n) → S s n ∧ n .vote = 0)
    (hJr : ∀ h j e r d n, X.get (h, j) = some e →
      Frame.stateAt (thread p L) X h j = some (some (.inr ⟨r, d⟩, n)) →
      J h (.inr ⟨r, d⟩, n) → 3 ≤ n .shfl)
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k pc : Nat} {s : Startup.D}
    {n : Cls → Nat} {j : Fin 3} {a r : Value} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl .idx a 0 31 r ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hS : StartAt L w s n) (hv : n .vote = 0) (hs : s.site = .sh j)
    (hprev : ∀ j, μ X j < μ X (g, k) → InWarp L w j.1 → ¬ Frame.Bad (thread p L) J X j) :
    r = b32 (if j.val = 0 then L.sharedBase else w) := by
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at hs
  subst hs
  obtain ⟨hns, -⟩ := hS
  obtain ⟨hcs, hcv⟩ := counts hσ
  have IH := upTo_of_lt hinit he rfl hprev
  rw [countColl, hcs, hcv, hv, hns] at IH
  have hK : X.ShflK (g, k) j.val := ⟨⟨_, _, _, _, _, _, _, he⟩, by rw [hcs, hns]⟩
  obtain ⟨-, hsrc⟩ := hX.shfl g k j.val pc .idx a 0 31 r ok he hK
  rw [shflSource_idx _ (by decide)] at hsrc
  dsimp only at hsrc
  obtain ⟨hT, hW, -, -, -⟩ := lane_facts hp hg hw (i := 0) (by decide)
  have hj3 := j.isLt
  -- a good state of the source lane at an event is a startup state or past three shuffles
  have cases : ∀ i e, X.get (g - laneOf L g + 0, i) = some e → (∀ pc f, e ≠ ⟨pc, .ub f⟩) →
      Frame.FollowedAt (thread p L) J X (g - laneOf L g + 0) i →
      ∃ σ n0, Frame.stateAt (thread p L) X (g - laneOf L g + 0) i = some (some (σ, n0)) ∧
        ((∃ s0, σ = .inl s0 ∧ S s0 n0 ∧ n0 .vote = 0) ∨ 3 ≤ n0 .shfl) := by
    intro i e hi hub hG
    obtain ⟨⟨σ, n0⟩, hσ0, hR0⟩ := good_state hp hX hi hub hG
    refine ⟨σ, n0, hσ0, ?_⟩
    rcases σ with s0 | ⟨r, d⟩
    · exact .inl ⟨s0, rfl, hJs _ _ _ hR0⟩
    · exact .inr (hJr _ _ _ _ _ _ hi hσ0 hR0)
  -- the source lane is at no ballot before an event with at most `j` shuffles before it
  have votes : ∀ i, Frame.cnt X Execution.isShfl (g - laneOf L g + 0) i ≤ j.val →
      Frame.cnt X isFullVote (g - laneOf L g + 0) i ≤ 0 := fun i hi =>
    Frame.coll_le (Good := Frame.FollowedAt (thread p L) J X (g - laneOf L g + 0))
      (fun i _ hn => IH _ i ⟨hT, hW⟩ (by simp only [Frame.cnt] at hn; rw [countColl]; omega))
      (fun i0 e0 he0 hv0 hG _ => by
        obtain ⟨σ, n0, hσ0, h0⟩ := cases i0 e0 he0
          (by rintro pc f rfl; simp [isFullVote, voteClass] at hv0) hG
        rcases h0 with ⟨s0, rfl, hS0, -⟩ | h3
        · have := (hSk _ _ _ _ hS0 (start_fired hp hX he0 hσ0).1).1
          rw [hv0] at this; cases this
        · have := (counts hσ0).1
          simp only [Frame.cnt]; omega) hi
  rcases hsrc with ⟨i, pc', b', c', r', o', hK', hi⟩ | ⟨kx, pcx, hx, hcx⟩
  · have hG := IH _ i ⟨hT, hW⟩ (by
      rw [countColl, hK'.2]; have := votes i (by simp only [Frame.cnt]; rw [hK'.2])
      simp only [Frame.cnt] at this; omega)
    obtain ⟨σ, n0, hσ0, h0⟩ := cases i _ hi (by rintro _ _ ⟨⟩) hG
    have hc0 := (counts hσ0).1
    rw [hK'.2] at hc0
    rcases h0 with ⟨s0, rfl, hS0, -⟩ | h3
    · have hS0 := hSsh _ _ hS0 (by omega)
      have hsite := startAt_site hS0 hc0.symm
      obtain ⟨_, _, hk⟩ := start_sent hp hW hS0 hsite (start_fired hp hX hi hσ0).1
      simp only [Kind.shfl.injEq] at hk
      exact hk.2.1
    · omega
  · exfalso
    have hG := IH _ kx ⟨hT, hW⟩ (by
      rw [countColl]; have := votes kx (by simp only [Frame.cnt]; omega)
      simp only [Frame.cnt] at this; omega)
    obtain ⟨σ, n0, hσ0, h0⟩ := cases kx _ hx (by rintro _ _ ⟨⟩) hG
    rcases h0 with ⟨s0, rfl, hS0, -⟩ | h3
    · exact (hSk _ _ _ _ hS0 (start_fired hp hX hx hσ0).1).2 rfl
    · have := (counts hσ0).1
      omega

theorem start_recv {J : (g : Nat) → (thread p L g).D → Prop} {w : Nat}
    (hinit : ∀ g, J g (thread p L g).init)
    (hJs : ∀ h s n, J h (.inl s, n) → StartAt L w s n ∧ n .vote = 0)
    (hJr : ∀ h j e r d n, X.get (h, j) = some e →
      Frame.stateAt (thread p L) X h j = some (some (.inr ⟨r, d⟩, n)) →
      J h (.inr ⟨r, d⟩, n) → 3 ≤ n .shfl)
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k pc : Nat} {s : Startup.D}
    {n : Cls → Nat} {j : Fin 3} {a r : Value} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl .idx a 0 31 r ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hS : StartAt L w s n) (hv : n .vote = 0) (hs : s.site = .sh j)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) J X j) :
    r = b32 (if j.val = 0 then L.sharedBase else w) :=
  start_recv_of (fun _ _ _ _ hS hE => ⟨(start_kind hS hE).1, (start_kind hS hE).2.1⟩)
    (fun _ _ h _ => h) hinit hJs hJr hp hX hg hw he hσ hS hv hs fun j hj => hprev j (.inl hj)

/-- The counts after a startup event: one more shuffle at a shuffle, one more event, and no
other class but the barrier's. -/
theorem start_bump {w : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartAt L w s n)
    (hE : Startup.Ev L g s e) (c : Cls) (hc : ¬ StartCls c) :
    Code.bump (cls L g) n e c = n c := by
  have := (start_kind hS hE).2.2.2.2 c
  by_cases h : cls L g c e = true
  · exact absurd (this h) hc
  · simp [Code.bump, h]

set_option maxHeartbeats 1000000 in
/-- **The startup steps a lane of warp `w` well before the barrier**: given that its shuffles
return the shared base and the warp index, the step is to a startup state that keeps `StartAt`. At
the barrier the step enters the role of the warp index (`enterOf`). -/
theorem start_next {w : Nat} (hp : Pre p L m) (hw : Prologue.warpIndex L g = w) (hw0 : w ≠ 0)
    (hw32 : w < 2 ^ 31) {s : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartAt L w s n)
    (hE : Startup.Ev L g s e)
    (hr : ∀ j : Fin 3, s.site = .sh j → ∀ pc a b c r ok, e = ⟨pc, .shfl .idx a b c r ok⟩ →
      r = b32 (if j.val = 0 then L.sharedBase else w)) :
    (thread p L g).next (.inl s, n) e ≠ some none ∧ ∀ σ', (thread p L g).next (.inl s, n) e =
      some (some σ') →
      (∃ s', σ'.1 = .inl s' ∧ StartAt L w s' σ'.2) ∨
        (s.site = .bar ∧
          σ'.1 = Code.enter (Startup.code p L g) (frag p L g) (exit L g)
            (Startup.enterOf s)) := by
  have hall : Code.bump (cls L g) n e .all = n .all + 1 := by simp [Code.bump, cls]
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site
  case sh j =>
    obtain ⟨r, ok, hk⟩ := start_sent hp hw hS rfl hE
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    have hr' := hr j rfl _ _ _ _ _ _ rfl
    have hsh : Code.bump (cls L g) n ⟨pc, .shfl .idx (b32 (if j.val = 0 then L.sharedBase else w))
        0 31 r ok⟩ .shfl = n .shfl + 1 := by
      simp [Code.bump, cls, Execution.isShfl]
    simp only [StartAt] at hS
    refine ⟨by simp [Startup.succ, hr', Startup.word32, b32], fun σ' h => .inl ?_⟩
    simp only [glued, Code.glue, Startup.code, Startup.succ, hr', Startup.word32, b32,
      Option.map_some, Option.some.injEq] at h
    subst h
    fin_cases j <;> simp only [Fin.isValue] at hS ⊢
    · exact ⟨_, rfl, by simp [Code.bump, cls, Execution.isShfl, hS.1],
        by simp [Code.bump, cls, hS.2.1],
        fun _ => rfl, by simp⟩
    · exact ⟨_, rfl, by simp [Code.bump, cls, Execution.isShfl, hS.1],
        by simp [Code.bump, cls, hS.2.1],
        fun _ => hS.2.2.1 (by decide), by simp⟩
    · have hne : Epilogue.scmpi .ne .b (BitVec.ofNat 64 w) 0 = true := by
        show Arith32.scmp .ne .b (Arith32.W w) (Arith32.W 0) = true
        rw [Arith32.scmp_ne_b_W (by omega) (by omega)]
        simpa using hw0
      simp only [show ((2 : ℕ) = 0) ↔ False by decide, hne, ↓reduceIte, Code.enter,
        exit]
      refine ⟨_, rfl, ?_⟩
      simp only [StartAt]
      exact ⟨by simp [Code.bump, cls, Execution.isShfl, hS.1], by simp [Code.bump, cls, hS.2.1],
        hS.2.2.1 (by decide), trivial⟩
  all_goals simp only [StartAt] at hS
  case fence =>
    simp only [Startup.Ev] at hE
    have hsh : Code.bump (cls L g) n e .shfl = n .shfl := by
      obtain ⟨pc, kind⟩ := e
      simp only at hE
      subst hE
      simp [Code.bump, cls, Execution.isShfl]
    refine ⟨by simp [Startup.succ], fun σ' h => .inl ?_⟩
    simp only [glued, Code.glue, Startup.code, Startup.succ, Option.map_some,
      Option.some.injEq, Code.enter, exit] at h
    subst h
    exact ⟨_, rfl, by simp only; rw [hsh, hS.1], by simp only; rw [hall, hS.2.1], hS.2.2.1,
      hS.2.2.2⟩
  case bar =>
    refine ⟨by simp [Startup.succ], fun σ' h => .inr ⟨rfl, ?_⟩⟩
    simp only [glued, Code.glue, Startup.code, Startup.succ, Option.map_some,
      Option.some.injEq] at h
    subst h
    rfl

/-- **The startup steps a lane of warp `w` well**, for a role's reference invariant `J` whose
startup states are `StartAt L w` with no ballot and the role's counts `Z`: up to the barrier the
startup's words and counts continue (the shuffles' values from `start_recv`), and after it the
role's facts `henter` hold. -/
theorem start_step_of {J : (g : Nat) → (thread p L g).D → Prop} {w : Nat}
    {Z : (Cls → Nat) → Prop} (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) (hw0 : w ≠ 0) (hw32 : w < 2 ^ 31)
    (hinit : ∀ g, J g (thread p L g).init)
    (hJs : ∀ s n, J g (.inl s, n) = (StartAt L w s n ∧ n .vote = 0 ∧ Z n))
    (hJs' : ∀ h s n, J h (.inl s, n) → StartAt L w s n ∧ n .vote = 0)
    (hJr : ∀ h j e r d n, X.get (h, j) = some e →
      Frame.stateAt (thread p L) X h j = some (some (.inr ⟨r, d⟩, n)) →
      J h (.inr ⟨r, d⟩, n) → 3 ≤ n .shfl)
    (hZ : ∀ n e, (∀ c, ¬ StartCls c → Code.bump (cls L g) n e c = n c) → Z n →
      Z (Code.bump (cls L g) n e))
    (henter : ∀ s n e, s.site = .bar → StartAt L w s n → n .vote = 0 → Z n →
      Startup.Ev L g s e → (∀ c, ¬ StartCls c → Code.bump (cls L g) n e c = n c) →
      J g (Code.enter (Startup.code p L g) (frag p L g) (exit L g) (Startup.enterOf s),
        Code.bump (cls L g) n e))
    {k : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hR : J g (.inl s, n))
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) J X j) :
    Frame.StepGood (thread p L) J g (.inl s, n) e := by
  have hE := (start_fired hp hX he hσ).1
  rw [hJs] at hR
  obtain ⟨hS, hv, hz⟩ := hR
  have hn := start_bump hS hE
  have hv' : Code.bump (cls L g) n e .vote = 0 := (hn _ (by simp [StartCls])).trans hv
  obtain ⟨hne, hsucc⟩ := start_next hp hw hw0 hw32 hS hE
    fun j hs pc a b c r ok hk => by
      obtain ⟨r', ok', hk'⟩ := start_sent hp hw hS hs hE
      rw [hk] at hk' he
      simp only [Kind.shfl.injEq] at hk'
      obtain ⟨-, rfl, rfl, rfl, -⟩ := hk'
      exact start_recv hinit hJs' hJr hp hX hg hw he hσ hS hv hs hprev
  refine ⟨hne, fun σ' h => ?_⟩
  obtain ⟨σ1, n1⟩ := σ'
  obtain ⟨-, rfl⟩ := Code.counted_next_some (C := glued p L g) h
  rcases hsucc _ h with ⟨s', hs', hS'⟩ | ⟨hb, hs'⟩
  · simp only at hs' hS'
    subst hs'
    rw [hJs]
    exact ⟨hS', hv', hZ n e hn hz⟩
  · simp only at hs'
    subst hs'
    exact henter s n e hb hS hv hz hE hn

end
end PTX.Kernels.TmlFa4Fwd.Proof
