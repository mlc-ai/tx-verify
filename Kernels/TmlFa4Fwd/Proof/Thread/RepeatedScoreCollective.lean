-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreIssue
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWait
import all Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
import Lemmas.Flow.CountTake
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame Correction TcMma

private theorem scoreCollectiveReleased {l : Launch} {X : Execution}
    {g j site : Nat} {kind : TcKind}
    (he : X.get (g,j) = some ⟨site,.tc kind⟩)
    (hKind : kind = .waitLd ∨ ∃ a words shape, kind = .ld a words shape)
    (hPeers : ∀ peer ∈ warpLanes l g, peer ≠ g → ∃ k,
      X.TcK (peer,k) (((X.tr g).take j).countP isTcColl))
    (hLast : j+1 = (X.tr g).length) : Step.Released l X g := by
  constructor
  intro pc actual hGet _
  have hIndex : (X.tr g).length-1 = j := by omega
  rw [hIndex,he,Option.some.injEq] at hGet
  cases hGet
  rw [hIndex]
  intro need hNeed
  have hSame : KindNeeds l X (.tc kind) (g,j) = tcNeeds l X (g,j) := by
    rcases hKind with rfl | ⟨_,_,_,rfl⟩ <;> rfl
  have hColl : isTcColl ⟨site,.tc kind⟩ = true := by
    rcases hKind with rfl | ⟨_,_,_,rfl⟩ <;> rfl
  simp only [Needs,he,hSame,tcNeeds] at hNeed
  obtain ⟨peer,hPeer,rfl⟩ := List.mem_map.mp hNeed
  by_cases hSelf : peer = g
  · subst peer
    exact ⟨.thread (g,j),⟨_,he⟩,j,rfl,⟨⟨_,he,hColl⟩,rfl⟩⟩
  · obtain ⟨k,hK⟩ := hPeers peer hPeer hSelf
    obtain ⟨event,hEvent,_⟩ := hK.1
    exact ⟨.thread (peer,k),⟨event,hEvent⟩,k,rfl,hK⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hGuard : SyncGuarded l kernel X)
    (hLayout : TcMma.LayoutInjective X) {g : Nat} (hg : g < l.threads) (round : Round)
    (quarter : Fin 4) (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (scorePc round quarter) F)
    (hAddress : (scoreReg round quarter,b32 (scoreAddress l g stage quarter)) ∈ F)
    (hWords : ∀ k < 32, ∀ v, TcMma.LastWrote l Assumptions.all X
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) k) v → v.bytes = 4)
    (hPeers : c.pos+1 = (X.tr g).length → ∀ peer ∈ warpLanes l g, peer ≠ g → ∃ k,
      X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl))
include hp hMax hGuard hLayout hg round quarter stage c hAddress hWords hPeers

/-- An issued score load returns once the matching warp occurrences are present.
On the ordinary route the decoded implicit wait is a second actual issue.
Peer occurrences are needed only when the lane's prefix ends at that collective. -/
theorem scoreLoadCollectiveRunOfMaximal :
    ∃ values ds, values.length = 32 ∧ ds.length = 32 ∧
      kernel.code[scorePc round quarter]? =
        some ⟨none,.tcLd ds (scoreReg round quarter) .s32x32b none⟩ ∧
      X.get (g,c.pos) = some
        ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) values .s32x32b)⟩ ∧
      (round = .unbiased → X.get (g,c.pos+1) = some ⟨scorePc round quarter,.tc .waitLd⟩) ∧
      let stop := if round = .unbiased then c.pos+2 else c.pos+1
      let u := setRegs (next c.ready) ds values
      Run kernel Assumptions.all l g {} ((X.tr g).take stop) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop stop) c.ending ∧
      (stop = (X.tr g).length →
        (round = .unbiased → ∀ peer ∈ warpLanes l g, peer ≠ g → ∃ k,
          X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl+1)) →
        Step.Released l X g) := by
  obtain ⟨values,ds,hValues,hDs,hCode,hIssue,hPast,hTail⟩ :=
    scoreLoadIssueWithStateOfMaximal hp hMax hGuard hLayout hg round quarter stage c hAddress hWords
  by_cases hPlain : round = .unbiased
  · let u := setRegs (next c.ready) ds values
    let s := {u with pc := c.ready.pc, sub := 1}
    have hs : s.pc = scorePc round quarter := c.checkpoint.1
    have hf : s.fault = none := (setRegsControl (next c.ready) ds values).1.trans
      c.checkpoint.2.2.2.1
    have hPending : out kernel Assumptions.all l g s = .ev (.tc .waitLd u) := by
      rw [out_event hf (hs.symm ▸ hCode) rfl rfl]
      change Out.ev (tcLdTmpl Assumptions.all l g s _) = _
      have hHook : Assumptions.all.any (·.tcLdWait s.pc) = true := by
        rw [hs,scoreWaitHook,decide_eq_true hPlain]
      simp only [tcLdTmpl,hHook,show s.sub ≠ 0 from Nat.one_ne_zero,↓reduceIte,s,next]
      have hSub : u.sub = 0 := (setRegsControl (next c.ready) ds values).2.trans c.checkpoint.2.1
      have hPc : u.pc = c.ready.pc+1 := setRegs_pc (next c.ready) ds values
      exact congrArg (fun v => Out.ev (.tc .waitLd v)) (resetPending hPc hSub)
    have hAvailable (hEnd : c.pos+1 = (X.tr g).length) :
        ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
      ⟨X,hMax,rfl,scoreCollectiveReleased hIssue (.inr ⟨_,_,_,rfl⟩) (hPeers hEnd) hEnd⟩
    obtain ⟨he,hRecorded,hRemaining⟩ := probabilityCollectiveOfMaximal hg (Nat.succ_pos _)
      (len_of_get hIssue) hPending rfl nofun
      (by simpa only [scoreLoadResume,hPlain,ite_true,s,u] using hPast)
      .refl (by simpa only [scoreLoadResume,hPlain,ite_true,s,u] using hTail) hAvailable
    have hWait : X.get (g,c.pos+1) = some ⟨scorePc round quarter,.tc .waitLd⟩ := by
      rwa [hs] at he
    have hOrdinal := countP_take_succ (p := isTcColl) hIssue rfl
    have hRelease (hEnd : c.pos+2 = (X.tr g).length)
        (hWaitPeers : round = .unbiased → ∀ peer ∈ warpLanes l g, peer ≠ g → ∃ k,
          X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl+1)) :
        Step.Released l X g :=
      scoreCollectiveReleased hWait (.inl rfl) (hOrdinal.symm ▸ hWaitPeers hPlain) hEnd
    exact ⟨values,ds,hValues,hDs,hCode,hIssue,fun _ => hWait,by
      simpa only [hPlain,ite_true,Nat.add_assoc] using And.intro hRecorded
        (And.intro hRemaining hRelease)⟩
  · refine ⟨values,ds,hValues,hDs,hCode,hIssue,fun h => (hPlain h).elim,?_⟩
    simpa only [hPlain,ite_false,scoreLoadResume] using And.intro hPast
      (And.intro hTail (fun hEnd _ =>
        scoreCollectiveReleased hIssue (.inr ⟨_,_,_,rfl⟩) (hPeers hEnd) hEnd))

end

private theorem scorePeerWarp {l : Launch} (hBlock : l.block % 32 = 0)
    {lead g peer : Nat} (hWarp : SameWarp l lead g) (hMem : peer ∈ warpLanes l g) :
    SameWarp l lead peer := by
  obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hMem
  have hRank : lane < 32 :=
    (List.mem_range.mp hLane).trans_le (min_le_left _ _)
  exact Step.sameWarp_trans hWarp (Step.sameWarp_lane hBlock hWarp.1.2.1 hRank).1

/-- Recorded load cursors of one warp supply each other's collective dependencies.
The input ordinals identify the same dynamic load across lanes. -/
theorem warpScoreLoadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : TcMma.LayoutInjective X)
    (lead ordinal : Nat) (round : Round) (quarter : Fin 4) (stage : Fin 2)
    {F : Nat → List (Nat × Value)}
    (c : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (scorePc round quarter) (F g))
    (hAddress : ∀ g, SameWarp l lead g →
      (scoreReg round quarter,b32 (scoreAddress l g stage quarter)) ∈ F g)
    (hRank : ∀ g (hWarp : SameWarp l lead g),
      ((X.tr g).take (c g hWarp).pos).countP isTcColl = ordinal)
    (hWords : ∀ g, SameWarp l lead g → ∀ k < 32, ∀ v, TcMma.LastWrote l Assumptions.all X
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) k) v → v.bytes = 4) :
    ∀ g (hWarp : SameWarp l lead g),
      let cur := c g hWarp
      ∃ values ds, values.length = 32 ∧ ds.length = 32 ∧
        kernel.code[scorePc round quarter]? =
          some ⟨none,.tcLd ds (scoreReg round quarter) .s32x32b none⟩ ∧
        X.get (g,cur.pos) = some
          ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) values .s32x32b)⟩ ∧
        (round = .unbiased → X.get (g,cur.pos+1) = some ⟨scorePc round quarter,.tc .waitLd⟩) ∧
        let stop := if round = .unbiased then cur.pos+2 else cur.pos+1
        let u := setRegs (next cur.ready) ds values
        Run kernel Assumptions.all l g {} ((X.tr g).take stop) (some u) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop stop) cur.ending ∧
        (stop = (X.tr g).length → Step.Released l X g) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLoads g (hWarp : SameWarp l lead g) : X.TcK (g,(c g hWarp).pos) ordinal := by
    obtain ⟨values,_,_,he,_,_⟩ :=
      scoreLoadIssueOfMaximal hp hMax hGuard hLayout hWarp.1.2.1 round quarter stage
        (c g hWarp) (hAddress g hWarp) (hWords g hWarp)
    exact ⟨⟨_,he,rfl⟩,hRank g hWarp⟩
  have hLoadPeers g (hWarp : SameWarp l lead g) :
      ∀ peer ∈ warpLanes l g, ∃ k,
        X.TcK (peer,k) (((X.tr g).take (c g hWarp).pos).countP isTcColl) := by
    intro peer hPeer
    rw [hRank g hWarp]
    exact ⟨_,hLoads peer (scorePeerWarp hBlock hWarp hPeer)⟩
  have hReturned g (hWarp : SameWarp l lead g) :=
    scoreLoadCollectiveRunOfMaximal hp hMax hGuard hLayout hWarp.1.2.1 round quarter stage
      (c g hWarp) (hAddress g hWarp) (hWords g hWarp)
      (fun _ peer hPeer _ => hLoadPeers g hWarp peer hPeer)
  intro g hWarp
  obtain ⟨values,ds,hValues,hDs,hCode,he,hWait,hPast,hTail,hRelease⟩ := hReturned g hWarp
  refine ⟨values,ds,hValues,hDs,hCode,he,hWait,hPast,hTail,fun hEnd => hRelease hEnd ?_⟩
  intro hPlain peer hPeer _
  have hSame := scorePeerWarp hBlock hWarp hPeer
  obtain ⟨words,_,_,_,_,hLoad,hPeerWait,_,_,_⟩ := hReturned peer hSame
  refine ⟨(c peer hSame).pos+1,⟨_,hPeerWait hPlain,rfl⟩,?_⟩
  rw [countP_take_succ (p := isTcColl) hLoad rfl,hRank peer hSame,hRank g hWarp]

end PTX.Kernels.TmlFa4Fwd.Softmax
