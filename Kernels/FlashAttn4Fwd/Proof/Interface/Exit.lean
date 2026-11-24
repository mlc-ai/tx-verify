-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc

@[expose] public section

/-! # What the thread layer exports for the exits

The CTAs exit without a cluster barrier; what orders a CTA's shared-memory uses before the
exit of the other CTA of its pair is the end of the Tensor Memory protocol. Barrier 2 (416
threads: the softmax warps 0–7, the correction warps 8–11 and the MMA warp 12) is used twice by
each of these threads: once after the allocation (a `bar.sync`), once after its last use of
Tensor Memory (the softmax's and correction's `bar.arrive`, the MMA warp's `bar.sync`). After its
second `bar.sync 2`, each lane of the MMA warp arrives on the other CTA's handshake barrier
(`+320`, release at cluster scope), waits on its own CTA's (acquire at cluster scope) and
deallocates; then it exits.

The fields are facts of single threads, from the run invariants of the softmax, correction, MMA
and loader roles and the sites of their barrier operations:

* barrier 2 is used only by warps 0–12 (`bar2_warp`), and each of them makes two barrier-2 events
  before its exit (`bar2_exit`);
* a thread polls only barriers of its own CTA (`wait_own`);
* a thread's use of the other CTA of its pair other than the handshake arrival, that is, an
  arrival on a barrier of another CTA or a commit (`PeerEvent`), comes before its second
  barrier-2 event (`peer_bar2`);
* the handshake arrival is a release at cluster scope after the thread's second barrier-2 event,
  a `bar.sync` (`hs_arrive`); a successful handshake poll acquires at cluster scope (`hs_wait`);
* a lane of the MMA warp exits after its handshake arrival on the other CTA's barrier and its
  successful poll of its own CTA's (`mma_exit`);
* at its handshake arrival, a lane of the leader CTA's MMA warp has polled each ring full barrier
  for every use of an item that passed the loop test (`mma_full`);
* at its exit, a softmax thread has polled its stage's S-full object for every score tile of an
  item that passed the loop test (`soft_exit`), and a correction thread each stage's O-full object
  for every such item (`corr_exit`);
* the MMA thread's MMAs, S-full and O-full commits are of items that passed the loop test: an MMA
  of stage `st` comes before the stage's O-full commit of its item (`mma_ofull`), a commit to an
  S-full object is of score tile `n` of item `n / kvBlocks` (`sfull_commit`), one to an O-full
  object of the item of its count (`ofull_commit`);
* a commit notifies a ring empty barrier, an S-full or an O-full object (`commit_target`);
* at its exit, the elected loader lane has polled its CTA's `qEmpty 1` once more than its
  `qEmpty 0` (the drain polls stage 1 only, `loader_q`); a commit to `qEmpty 0` is at site 995,
  and the MMA thread's commit to `qEmpty 1` of the same use is its next commit (`q_next`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- An event of thread `g` that uses the other CTA of its pair, other than the handshake
arrival: an arrival on a barrier of another CTA that is not a handshake barrier, or a commit. -/
def PeerEvent (L : Launch) (g : Nat) (ev : Event) : Prop :=
  (∃ m tx cnt rel sc, ev.kind = .arrive m tx cnt rel sc ∧ m.cta ≠ ctaOf L g ∧
    m ≠ FBar.loc L m.cta .dealloc) ∨
  ∃ sp, ev.kind = .tc (.commit sp)

/-- The thread layer's facts for the exits. -/
structure ExitFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- An event on barrier 2 is a thread's of warps 0–12. -/
  bar2_warp : ∀ {g i pc : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩ → warpOf L g < 13
  /-- A thread of warps 0–12 exits after two events on barrier 2. -/
  bar2_exit : ∀ {g k pc : Nat}, g < L.threads → warpOf L g < 13 →
    X.get (g, k) = some ⟨pc, .exit⟩ → 2 ≤ barOrd X g k 2
  /-- A poll names a barrier of its thread's CTA. -/
  wait_own : ∀ {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ → m.cta = ctaOf L g
  /-- A use of the other CTA but the handshake arrival comes before the thread's second event on
  barrier 2. -/
  peer_bar2 : ∀ {g k : Nat} {ev : Event}, g < L.threads → X.get (g, k) = some ev →
    PeerEvent L g ev → warpOf L g < 13 ∧ barOrd X g k 2 ≤ 1
  /-- A handshake arrival is a release at cluster scope, after the thread's second event on
  barrier 2, a `bar.sync`. -/
  hs_arrive : ∀ {g k pc tx cnt cta : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, k) = some ⟨pc, .arrive (FBar.loc L cta .dealloc) tx cnt rel sc⟩ →
      rel = true ∧ sc = .cluster ∧
        ∃ i < k, ∃ pci cnti, X.IsBarrier (g, i) 2 cnti pci ∧ barOrd X g i 2 = 1
  /-- A successful handshake poll acquires at cluster scope. -/
  hs_wait : ∀ {g k pc p cta : Nat} {acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, k) = some ⟨pc, .wait (FBar.loc L cta .dealloc) p true acq sc⟩ →
      acq = true ∧ sc = .cluster
  /-- A lane of warp 12 exits after its arrival on the other CTA's handshake barrier and a
  successful poll of its own CTA's. -/
  mma_exit : ∀ {g k pc : Nat}, g < L.threads → warpOf L g = 12 →
    X.get (g, k) = some ⟨pc, .exit⟩ →
      ∃ a w, a < w ∧ w < k ∧
        (∃ pca tx cnt rel sc, X.get (g, a) =
          some ⟨pca, .arrive (FBar.loc L (pairCta (ctaOf L g)) .dealloc) tx cnt rel sc⟩) ∧
        ∃ pcw acq sc, X.get (g, w) =
          some ⟨pcw, .wait (FBar.loc L (ctaOf L g) .dealloc) 0 true acq sc⟩
  /-- At its handshake arrival, a lane of the even CTA's warp 12 has made a successful poll of a
  ring full barrier of its CTA for every use whose item passed the loop test. -/
  mma_full : ∀ {g a pc tx cnt u : Nat} {rel : Bool} {sc : MbarScope} {b : FBar},
    g < L.threads → warpOf L g = 12 → ctaOf L g % 2 = 0 →
    X.get (g, a) = some ⟨pc, .arrive (FBar.loc L (pairCta (ctaOf L g)) .dealloc) tx cnt rel sc⟩ →
    b.isFull → workOf L g (useItem P b u) < totOf L →
      u < okPolls (b.loc L (ctaOf L g)) ((X.tr g).take a)
  /-- At its exit, a softmax thread has polled its stage's S-full object of its CTA for every score
  tile of an item that passed the loop test. -/
  soft_exit : ∀ {g k pc u : Nat}, g < L.threads → warpOf L g < 8 →
    X.get (g, k) = some ⟨pc, .exit⟩ → workOf L g (u / kvBlocks P) < totOf L →
      u < okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take k)
  /-- At its exit, a correction thread has polled each stage's O-full object of its CTA for every
  item that passed the loop test. -/
  corr_exit : ∀ {g k pc u st : Nat}, g < L.threads → 8 ≤ warpOf L g → warpOf L g < 12 →
    X.get (g, k) = some ⟨pc, .exit⟩ → st < 2 → workOf L g u < totOf L →
      u < okPolls (oFullBar L (ctaOf L g) st) ((X.tr g).take k)
  /-- An MMA of stage `st` comes before the stage's O-full commit of its item, which passed the
  loop test. -/
  mma_ofull : ∀ {g k d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue (g, k) d s acc mask → ∃ st < 2,
      workOf L g (((X.tr g).take k).countP (commitsTo (oFullBar L (ctaOf L g) st))) < totOf L
  /-- A commit to an S-full object is of score tile `n` (its earlier commits there) of item
  `n / kvBlocks`, which passed the loop test. -/
  sfull_commit : ∀ {g k pc st : Nat} {sp : TcCommit.Spec}, g < L.threads → st < 2 →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = sFullBar L (ctaOf L g) st →
      workOf L g (((X.tr g).take k).countP (commitsTo sp.mbar) / kvBlocks P) < totOf L
  /-- A commit to an O-full object is of the item of its earlier commits there, which passed the
  loop test. -/
  ofull_commit : ∀ {g k pc st : Nat} {sp : TcCommit.Spec}, g < L.threads → st < 2 →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFullBar L (ctaOf L g) st →
      workOf L g (((X.tr g).take k).countP (commitsTo sp.mbar)) < totOf L
  /-- A commit notifies a ring empty barrier, an S-full or an O-full object. -/
  commit_target : ∀ {g k pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m →
      ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ (b.isEmpty ∨ ∃ st, b = .sFull st ∨ b = .oFull st)
  /-- At its exit, an elected loader lane has polled its CTA's `qEmpty 1` once more than its
  `qEmpty 0` (the drain). -/
  loader_q : ∀ {g k pc : Nat}, g < L.threads → warpOf L g = 14 → LeadAt L X g k →
    X.get (g, k) = some ⟨pc, .exit⟩ →
      okPolls (FBar.loc L (ctaOf L g) (.qEmpty 1)) (X.tr g) =
        okPolls (FBar.loc L (ctaOf L g) (.qEmpty 0)) (X.tr g) + 1
  /-- A commit to `qEmpty 0` is at site `995`; the thread's commit to `qEmpty 1` with as many
  earlier commits there follows it with no commit between. -/
  q_next : ∀ {g j j' pc pc' : Nat} {sp sp' : TcCommit.Spec}, g < L.threads →
    X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = FBar.loc L (ctaOf L g) (.qEmpty 0) →
      pc = 995 ∧
      (X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ →
        sp'.mbar = FBar.loc L (ctaOf L g) (.qEmpty 1) →
        ((X.tr g).take j').countP (commitsTo sp'.mbar) =
          ((X.tr g).take j).countP (commitsTo sp.mbar) →
        j < j' ∧ ∀ k, j < k → k < j' → ∀ pck spk, X.get (g, k) ≠ some ⟨pck, .tc (.commit spk)⟩)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
