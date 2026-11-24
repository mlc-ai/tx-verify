-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.SoftmaxLaneStep
public import Kernels.TmlFa4Fwd.Proof.Progress.RecurringBiasAcquire
public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasEmptyRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread Softmax

/-- The arrivals a softmax lane has made before the head of visit `visit`: one main probability
credit per earlier visit; one tail credit per earlier visit when it is the elected leader of its
warp (the leader of every full-mask election of the warp); and, on lane zero, one Bias-empty
release per earlier biased visit, the opening visit included. -/
def HeadArrivals (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2)
    (biased g visit pos : Nat) : Prop :=
  visit ≤ arrivals (Scores.probabilityObject l cta stage 0) ((X.tr g).take pos) ∧
  (∃ leader, (∃ i pc inst, X.Elect (g,i) pc (2^32-1) inst leader) ∧
    (laneOf l g = leader →
      visit ≤ arrivals (Scores.probabilityObject l cta stage 1) ((X.tr g).take pos))) ∧
  (laneOf l g = 0 →
    min visit biased ≤ arrivals (Loader.biasEmptyObject l cta stage) ((X.tr g).take pos))

theorem getOfTrace {X Y : Execution} (h : Y.tr = X.tr) (i : EvId) : Y.get i = X.get i := by
  simp only [Execution.get,h]

/-- An event of the trace that satisfies a marker raises its count past every earlier
prefix. -/
theorem countP_take_lt_of_mark {X : Execution} {g a c b : Nat} {mark : Event → Bool}
    {e : Event} (he : X.get (g,c) = some e) (hm : mark e = true) (ha : a ≤ c) (hb : c < b) :
    ((X.tr g).take a).countP mark+1 ≤ ((X.tr g).take b).countP mark := by
  have h1 := countP_take_mono mark (X.tr g) ha
  have h2 := countP_take_succ he hm
  have h3 := countP_take_mono mark (X.tr g) (show c+1 ≤ b by omega)
  omega

theorem arrivesOn_of_arrive {X : Execution} {i : EvId} {m : Loc} {tx c : Nat} {rel : Bool}
    {sc : MbarScope} (h : X.Arrive i m tx c rel sc) :
    ∃ e, X.get i = some e ∧ arrivesOn m e = true := by
  obtain ⟨pc,he⟩ := h
  exact ⟨_,he,by simp [arrivesOn,sourceArrive]⟩

/-- The whole trace counts at least as many arrivals as any prefix. -/
theorem arrivals_take_le (m : Loc) (es : List Event) (n : Nat) :
    arrivals m (es.take n) ≤ arrivals m es := by
  unfold arrivals
  exact (List.take_sublist n es).countP_le

/-- Two full-mask elections of one lane return the same leader. -/
theorem leader_eq_of_elections {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j pc pc' inst inst' a b : Nat}
    (hg : g < l.threads) (ha : X.Elect (g,i) pc (2^32-1) inst a)
    (hb : X.Elect (g,j) pc' (2^32-1) inst' b) : a = b :=
  hX.elect.2.2 _ _ _ _ _ _ _ _ _ ha hb ⟨⟨hg,hg,rfl⟩,rfl⟩

/-- What a stage visit leaves behind for the other roles: every lane's statistics publication
of the visit, its main probability credits, the leader's tail credits and lane zero's
Bias-empty releases. -/
structure StageVisitOutputs (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2)
    (biased visit : Nat) : Prop where
  published : ∀ g, BiasedStageMember l cta stage g → ∃ i r, Scores.Publishes X (g,i) r ∧
    visit ≤ observedBarrierOrdinal X (g,i) (3+warpIndex l g)
  main : ∀ g, BiasedStageMember l cta stage g →
    visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 0) (X.tr g)
  tail : ∀ g, BiasedStageMember l cta stage g → ∀ leader,
    (∃ i pc inst, X.Elect (g,i) pc (2^32-1) inst leader) → laneOf l g = leader →
      visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 1) (X.tr g)
  bias : visit < biased → ∀ g, BiasedStageMember l cta stage g → laneOf l g = 0 →
    visit+1 ≤ arrivals (Loader.biasEmptyObject l cta stage) (X.tr g)

/-- The facts a lane's visit provides at its join, before the correction credit. -/
private structure LaneJoinFacts (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2)
    (biased g visit head join : Nat) : Prop where
  published : ∃ i r, Scores.Publishes X (g,i) r ∧ head < i ∧ i < join
  main : ∃ i, X.Arrive (g,i) (Scores.probabilityObject l cta stage 0) 0 1 true .cta ∧
    head ≤ i ∧ i < join
  tail : ∃ leader, (∃ i pc inst, X.Elect (g,i) pc (2^32-1) inst leader) ∧
    (laneOf l g = leader → ∃ i,
      X.Arrive (g,i) (Scores.probabilityObject l cta stage 1) 0 1 true .cta ∧
      head ≤ i ∧ i < join)
  bias : visit < biased → laneOf l g = 0 → ∃ e i, X.get (g,i) = some e ∧
    arrivesOn (Loader.biasEmptyObject l cta stage) e = true ∧ head ≤ i ∧ i < join

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem outputsOfJoin (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {stage : Fin 2} {biased g visit head join : Nat}
    (hm : BiasedStageMember l cta stage g) (arr : HeadArrivals l X cta stage biased g visit head)
    (notices : ((X.tr g).take head).countP Scores.publishesStats = visit)
    (J : LaneJoinFacts l X cta stage biased g visit head join) :
    (∃ i r, Scores.Publishes X (g,i) r ∧ visit ≤ observedBarrierOrdinal X (g,i) (3+warpIndex l g))
      ∧ visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 0) (X.tr g) ∧
      (∀ leader, (∃ i pc inst, X.Elect (g,i) pc (2^32-1) inst leader) → laneOf l g = leader →
        visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 1) (X.tr g)) ∧
      (visit < biased → laneOf l g = 0 →
        visit+1 ≤ arrivals (Loader.biasEmptyObject l cta stage) (X.tr g)) ∧
      ∀ pos, join ≤ pos → HeadArrivals l X cta stage biased g (visit+1) pos := by
  have hw := hm.2.2.1
  obtain ⟨i,r,hPub,hLo,_⟩ := J.published
  have hOrd : visit ≤ observedBarrierOrdinal X (g,i) (3+warpIndex l g) := by
    have e : ((X.tr g).take i).countP Scores.publishesStats =
        ((X.tr g).take i).countP (Execution.isBarId (3+warpIndex l g)) := by
      have h := Scores.notificationOrdinal hp hX (g := g) (j := i) hw
      rwa [Scores.beforeNotices,Scores.barrierOrdinal] at h
    show visit ≤ ((X.tr g).take i).countP (Execution.isBarId (3+warpIndex l g))
    have := countP_take_mono Scores.publishesStats (X.tr g) hLo.le
    omega
  obtain ⟨mi,hMain,hMLo,hMHi⟩ := J.main
  obtain ⟨me,hMe,hMm⟩ := arrivesOn_of_arrive hMain
  obtain ⟨leader,hElect,hTail⟩ := J.tail
  obtain ⟨hA0,⟨leader₀,hElect₀,hA1⟩,hA2⟩ := arr
  have hSame : leader₀ = leader := by
    obtain ⟨i₀,pc₀,inst₀,h₀⟩ := hElect₀
    obtain ⟨i₁,pc₁,inst₁,h₁⟩ := hElect
    exact leader_eq_of_elections hX hm.1 h₀ h₁
  subst hSame
  have mainAt (pos : Nat) (hp : join ≤ pos) :
      visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 0) ((X.tr g).take pos) :=
    hA0.trans_lt (countP_take_lt_of_mark hMe hMm hMLo (by omega))
  refine ⟨⟨i,r,hPub,hOrd⟩,?_,?_,?_,?_⟩
  · have h1 := mainAt join le_rfl
    have h3 := arrivals_take_le (Scores.probabilityObject l cta stage 0) (X.tr g) join
    omega
  · intro leader' hElect' hLead
    obtain ⟨i₀,pc₀,inst₀,h₀⟩ := hElect₀
    obtain ⟨i₁,pc₁,inst₁,h₁⟩ := hElect'
    have e := leader_eq_of_elections hX hm.1 h₀ h₁
    subst e
    obtain ⟨ti,hT,hTLo,hTHi⟩ := hTail hLead
    obtain ⟨te,hTe,hTm⟩ := arrivesOn_of_arrive hT
    have h1 := hA1 hLead
    have h2 := countP_take_lt_of_mark hTe hTm hTLo hTHi
    have h3 := arrivals_take_le (Scores.probabilityObject l cta stage 1) (X.tr g) join
    unfold arrivals at h1 h3 ⊢
    omega
  · intro hB hLane
    obtain ⟨be,bi,hBe,hBm,hBLo,hBHi⟩ := J.bias hB hLane
    have h := hA2 hLane
    rw [Nat.min_eq_left hB.le] at h
    have h2 := countP_take_lt_of_mark hBe hBm hBLo hBHi
    have h3 := arrivals_take_le (Loader.biasEmptyObject l cta stage) (X.tr g) join
    unfold arrivals at h h3 ⊢
    omega
  · intro pos hPos
    refine ⟨mainAt pos hPos,⟨leader₀,hElect₀,fun hLead => ?_⟩,fun hLane => ?_⟩
    · obtain ⟨ti,hT,hTLo,hTHi⟩ := hTail hLead
      obtain ⟨te,hTe,hTm⟩ := arrivesOn_of_arrive hT
      exact (hA1 hLead).trans_lt (countP_take_lt_of_mark hTe hTm hTLo (by omega))
    · by_cases hB : visit < biased
      · obtain ⟨be,bi,hBe,hBm,hBLo,hBHi⟩ := J.bias hB hLane
        have h := hA2 hLane
        rw [Nat.min_eq_left hB.le] at h
        have := countP_take_lt_of_mark hBe hBm hBLo (show bi < pos by omega)
        unfold arrivals at h ⊢
        omega
      · have h := hA2 hLane
        have := countP_take_mono (arrivesOn (Loader.biasEmptyObject l cta stage)) (X.tr g)
          (show head ≤ pos by omega)
        unfold arrivals at h ⊢
        omega

private theorem publishesOfTrace {X Y : Execution} (h : Y.tr = X.tr) {i : EvId}
    {r : Scores.Round} (hp : Scores.Publishes Y i r) : Scores.Publishes X i r := by
  obtain ⟨e,he,hn⟩ := hp
  exact ⟨e,(getOfTrace h i).symm.trans he,hn⟩

private theorem arriveOfTrace {X Y : Execution} (h : Y.tr = X.tr) {i : EvId} {m : Loc}
    {tx c : Nat} {rel : Bool} {sc : MbarScope} (ha : Y.Arrive i m tx c rel sc) :
    X.Arrive i m tx c rel sc := by
  obtain ⟨pc,he⟩ := ha
  exact ⟨pc,(getOfTrace h i).symm.trans he⟩

private theorem electOfTrace {X Y : Execution} (h : Y.tr = X.tr) {i : EvId}
    {pc mask inst leader : Nat} (he : Y.Elect i pc mask inst leader) :
    X.Elect i pc mask inst leader :=
  (getOfTrace h i).symm.trans he

/-- A whole stage at the heads of a biased visit, with its score and Bias generation
delivered, publishes the visit; after the correction credits of the visit every lane reaches
its next head or the terminal statistics. -/
theorem biasedStageStep (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {cta : Nat}
    (hc : cta < l.grid) (stage : Fin 2) {trips split visit : Nat} (hTrips : trips < 2^31)
    (hVisit : 1 ≤ visit) (hBiased : visit < trips-split) (barsW electsW : Nat → Nat)
    (heads : ∀ g, BiasedStageMember l cta stage g → ∃ pos,
      LoopHeadAt p l X trips split g (warpOf l g) visit (barsW (warpIndex l g))
        (electsW (warpIndex l g)) pos ∧ HeadArrivals l X cta stage (trips-split) g visit pos)
    (score : ∃ issue spec, Scores.ScoreCommit l X issue cta stage spec 0 ∧
      Scores.scoreCommitOrdinal l X cta stage issue = visit ∧ (0 : Fin 16) ∈ X.tcNotified issue)
    (bias : BiasGenerationDelivered l X cta stage visit) :
    StageVisitOutputs l X cta stage (trips-split) visit ∧
      (Protocol.Statistics.TerminalCorrectionCredits l X cta stage visit →
        ∀ g, BiasedStageMember l cta stage g → ∃ pos,
          LoopNextAt p l X trips split g (warpOf l g) visit (barsW (warpIndex l g))
            (electsW (warpIndex l g)) pos ∧
          HeadArrivals l X cta stage (trips-split) g (visit+1) pos) := by
  classical
  have hB (g : Nat) : ∃ (block floor counter : Nat) (maximum : Option ℝ) (sum : ℝ),
      BiasedStageMember l cta stage g → counter = 2^32-(trips-split)+(visit-1) ∧
        ∃ h : BiasedLoopHead p l X g (warpOf l g) visit block floor counter
          (barsW (warpIndex l g)) (electsW (warpIndex l g)) maximum sum,
          h.split = split ∧ HeadArrivals l X cta stage (trips-split) g visit h.cursor.pos := by
    by_cases hm : BiasedStageMember l cta stage g
    · obtain ⟨pos,hL,hA⟩ := heads g hm
      rcases hL with ⟨_,block,floor,counter,mx,sm,hCnt,h,hPos,hs⟩ | ⟨hLe,_⟩
      · exact ⟨block,floor,counter,mx,sm,fun _ => ⟨hCnt,h,hs,hPos ▸ hA⟩⟩
      · omega
    · exact ⟨0,0,0,none,0,fun h => absurd h hm⟩
  choose block floor counter maximum sum H using hB
  let head (g : Nat) (hm : BiasedStageMember l cta stage g) := Classical.choose (H g hm).2
  have hHead (g : Nat) (hm : BiasedStageMember l cta stage g) :=
    Classical.choose_spec (H g hm).2
  have hScore (g : Nat) (hm : BiasedStageMember l cta stage g) :
      okPolls (Scores.scoreReadyObject l (g/l.block) stage) (X.tr g) = visit →
        OpeningPollReady X (Scores.scoreReadyObject l (g/l.block) stage) (visit%2) :=
    scoreReadyForPendingLane hp hMax (frame X hMax.1) hm.2.2.1 stage hm.2.2.2
      (by rw [hm.2.1]; exact score)
  have hBiasReady (g : Nat) (hm : BiasedStageMember l cta stage g) :
      (X.tr g).countP (Execution.isBarId (11+stage.val)) = visit →
        ∀ {t}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
          OpeningPollReady X (waitLoc l g stage 5) (visit%2) := fun rank _ run =>
    BiasGenerationDelivered.readyForPendingLane hp hMax (by rw [hm.2.1]; exact bias)
      ((Thread.biasParticipantIff ..).mpr ⟨hm.2.2.1,hm.2.2.2⟩) rank run
  obtain ⟨Y₁,hY₁,hT₁,hO₁,out⟩ := stageBiasedJoinsOfHeads hp hMax frame hc stage visit block
    floor counter barsW electsW maximum sum head hScore hBiasReady
  have lane (g : Nat) (hm : BiasedStageMember l cta stage g) :
      ∃ Y₂, Maximal l kernel Assumptions.all m Y₂ ∧ Y₂.tr = X.tr ∧ Y₂.objects = X.objects ∧
        ∃ start, ∃ bias : Nat → Option ℝ, ∃ dot : Nat → ℝ,
        ∃ J : BiasedVisitJoin p l Y₁ Y₂ g (warpOf l g) visit start
          ((block g+(2^32-1))%2^32) (counter g) (barsW (warpIndex l g))
          (electsW (warpIndex l g)) (maximum g) (sum g) bias dot,
          (head g hm).cursor.pos < J.join.cursor.pos ∧
          LaneJoinFacts l X cta stage (trips-split) g visit (head g hm).cursor.pos
            J.join.cursor.pos := by
    obtain ⟨Y₂,hY₂,hT₂,hO₂,start,biasF,dotF,J,hOrd,hStart,hLane0⟩ := out g hm
    refine ⟨Y₂,hY₂,hT₂,hO₂,start,biasF,dotF,J,hOrd,?_,?_,?_,?_⟩
    · have hMain := J.mainBefore
      exact ⟨start+1,_,publishesOfTrace hT₁ J.published,by omega,by omega⟩
    · have h := arriveOfTrace hT₂ J.mainCredit
      rw [hm.2.1,hm.stage] at h
      exact ⟨_,h,by omega,J.mainBefore⟩
    · obtain ⟨inst,hE⟩ := J.elected
      refine ⟨J.leader.val,⟨_,_,_,electOfTrace hT₂ hE⟩,fun hLead => ?_⟩
      have h := arriveOfTrace hT₂ (J.tailCredit hLead)
      rw [hm.2.1,hm.stage] at h
      exact ⟨_,h,by omega,J.tailBefore hLead⟩
    · intro _ hLane
      have he := (getOfTrace hT₁ _).symm.trans (hLane0 hLane)
      refine ⟨_,start-1,he,?_,by omega,by have := J.mainBefore; omega⟩
      rw [Protocol.Bias.biasReleaseLoc,hm.2.1]
      simp [arrivesOn,sourceArrive]
  have facts (g : Nat) (hm : BiasedStageMember l cta stage g) :
      (∃ i r, Scores.Publishes X (g,i) r ∧
        visit ≤ observedBarrierOrdinal X (g,i) (3+warpIndex l g)) ∧
      visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 0) (X.tr g) ∧
      (∀ leader, (∃ i pc inst, X.Elect (g,i) pc (2^32-1) inst leader) → laneOf l g = leader →
        visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 1) (X.tr g)) ∧
      (visit < trips-split → laneOf l g = 0 →
        visit+1 ≤ arrivals (Loader.biasEmptyObject l cta stage) (X.tr g)) := by
    obtain ⟨_,_,_,_,_,_,_,J,_,F⟩ := lane g hm
    obtain ⟨a,b,c,d,_⟩ := outputsOfJoin hp hMax.1 hm (hHead g hm).2 (head g hm).counts.2.2.2.1 F
    exact ⟨a,b,c,d⟩
  refine ⟨⟨fun g hm => (facts g hm).1,fun g hm => (facts g hm).2.1,
    fun g hm => (facts g hm).2.2.1,fun hB g hm => (facts g hm).2.2.2 hB⟩,?_⟩
  intro credits g hm
  obtain ⟨Y₂,hY₂,hT₂,hO₂,start,biasF,dotF,J,hOrd,F⟩ := lane g hm
  have hCredits : Protocol.Statistics.TerminalCorrectionCredits l X (g/l.block)
      (stageOf (warpOf l g)) visit := by rw [hm.2.1,hm.stage]; exact credits
  obtain ⟨pos,hPos,hNext⟩ := biasedLaneNext hp hMax hY₂ hT₂ hO₂ (frame X hMax.1) hm.1 hm.warp
    (head g hm) (H g hm).1 (hHead g hm).1 hVisit hBiased hTrips J hOrd hCredits
  exact ⟨pos,hNext,(outputsOfJoin hp hMax.1 hm (hHead g hm).2 (head g hm).counts.2.2.2.1
    F).2.2.2.2 pos hPos.le⟩

/-- A whole stage at the heads of a plain visit, with its score delivered, publishes the visit;
after the correction credits of the visit every lane reaches its next head or the terminal
statistics. -/
theorem plainStageStep (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {cta : Nat}
    (stage : Fin 2) {trips split visit : Nat} (hTrips : trips < 2^31) (hSplitLe : split ≤ trips)
    (hPlain : trips-split ≤ visit) (hLt : visit < trips) (barsW electsW : Nat → Nat)
    (heads : ∀ g, BiasedStageMember l cta stage g → ∃ pos,
      LoopHeadAt p l X trips split g (warpOf l g) visit (barsW (warpIndex l g))
        (electsW (warpIndex l g)) pos ∧ HeadArrivals l X cta stage (trips-split) g visit pos)
    (score : ∃ issue spec, Scores.ScoreCommit l X issue cta stage spec 0 ∧
      Scores.scoreCommitOrdinal l X cta stage issue = visit ∧
      (0 : Fin 16) ∈ X.tcNotified issue) :
    StageVisitOutputs l X cta stage (trips-split) visit ∧
      (Protocol.Statistics.TerminalCorrectionCredits l X cta stage visit →
        ∀ g, BiasedStageMember l cta stage g → ∃ pos,
          LoopNextAt p l X trips split g (warpOf l g) visit (barsW (warpIndex l g))
            (electsW (warpIndex l g)) pos ∧
          HeadArrivals l X cta stage (trips-split) g (visit+1) pos) := by
  classical
  let tc := 11*(trips-split)+14*(visit-(trips-split))
  have hB (g : Nat) : ∃ (counter : Nat) (maximum : Option ℝ) (sum : ℝ),
      BiasedStageMember l cta stage g → counter = 2^32-split+(visit-(trips-split)) ∧
        ∃ h : PlainLoopAt p l X g (warpOf l g) 6661 visit counter tc
          (barsW (warpIndex l g)) (electsW (warpIndex l g)) maximum sum,
          HeadArrivals l X cta stage (trips-split) g visit h.cursor.pos := by
    by_cases hm : BiasedStageMember l cta stage g
    · obtain ⟨pos,hL,hA⟩ := heads g hm
      rcases hL with ⟨hLt',_⟩ | ⟨_,counter,tc',mx,sm,hCnt,hTc,h,hPos⟩
      · omega
      · subst hTc
        exact ⟨counter,mx,sm,fun _ => ⟨hCnt,h,hPos ▸ hA⟩⟩
    · exact ⟨0,none,0,fun h => absurd h hm⟩
  choose counter maximum sum H using hB
  let head (g : Nat) (hm : BiasedStageMember l cta stage g) := Classical.choose (H g hm).2
  have hHead (g : Nat) (hm : BiasedStageMember l cta stage g) :=
    Classical.choose_spec (H g hm).2
  have lane (g : Nat) (hm : BiasedStageMember l cta stage g) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
        ∃ start, ∃ J : PlainVisitJoin p l X Y g (warpOf l g) visit start (counter g) tc
          (barsW (warpIndex l g)) (electsW (warpIndex l g)) (maximum g) (sum g),
          (head g hm).cursor.pos < J.join.cursor.pos ∧
          LaneJoinFacts l X cta stage (trips-split) g visit (head g hm).cursor.pos
            J.join.cursor.pos := by
    have T (h : Nat) (hw : SameWarp l g h) :
        ∃ hh : PlainLoopAt p l X h (warpOf l g) 6661 visit (counter h) tc
          (barsW (warpIndex l g)) (electsW (warpIndex l g)) (maximum h) (sum h),
          hh.cursor.pos = (head h (hm.ofSameWarp hw)).cursor.pos := by
      have e : warpIndex l g = warpIndex l h := hw.2
      rw [← warpOf_sameWarp hw,e]
      exact ⟨_,rfl⟩
    choose heads' hPos' using T
    have hScore (h : Nat) (hw : SameWarp l g h) :
        okPolls (Scores.scoreReadyObject l (h/l.block) (stageOf (warpOf l g))) (X.tr h) =
          visit → OpeningPollReady X
            (Scores.scoreReadyObject l (h/l.block) (stageOf (warpOf l g))) (visit%2) := by
      have hh := hm.ofSameWarp hw
      rw [hm.stage]
      exact scoreReadyForPendingLane hp hMax (frame X hMax.1) hh.2.2.1 stage hh.2.2.2
        (by rw [hh.2.1]; exact score)
    obtain ⟨Y,hY,hT,hO,joins⟩ := warpPlainJoinsOfHeads hp hMax (frame X hMax.1) hm.2.2.1 visit
      tc (barsW (warpIndex l g)) (electsW (warpIndex l g)) counter maximum sum heads' hScore
    have self : SameWarp l g g := ⟨⟨hm.1,hm.1,rfl⟩,rfl⟩
    obtain ⟨start,J,hOrd,hStart⟩ := joins g self
    rw [hPos'] at hOrd hStart
    refine ⟨Y,hY,hT,hO,start,J,hOrd,?_,?_,?_,?_⟩
    · have hMain := J.mainBefore
      exact ⟨start+9,_,J.published,by omega,by omega⟩
    · have h := arriveOfTrace hT J.mainCredit
      rw [hm.2.1,hm.stage] at h
      exact ⟨_,h,by omega,J.mainBefore⟩
    · obtain ⟨inst,hE⟩ := J.elected
      refine ⟨J.leader.val,⟨_,_,_,electOfTrace hT hE⟩,fun hLead => ?_⟩
      have h := arriveOfTrace hT (J.tailCredit hLead)
      rw [hm.2.1,hm.stage] at h
      exact ⟨_,h,by omega,J.tailBefore hLead⟩
    · intro hB
      omega
  have facts (g : Nat) (hm : BiasedStageMember l cta stage g) :
      (∃ i r, Scores.Publishes X (g,i) r ∧
        visit ≤ observedBarrierOrdinal X (g,i) (3+warpIndex l g)) ∧
      visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 0) (X.tr g) ∧
      (∀ leader, (∃ i pc inst, X.Elect (g,i) pc (2^32-1) inst leader) → laneOf l g = leader →
        visit+1 ≤ arrivals (Scores.probabilityObject l cta stage 1) (X.tr g)) ∧
      (visit < trips-split → laneOf l g = 0 →
        visit+1 ≤ arrivals (Loader.biasEmptyObject l cta stage) (X.tr g)) := by
    obtain ⟨_,_,_,_,_,J,_,F⟩ := lane g hm
    obtain ⟨a,b,c,d,_⟩ := outputsOfJoin hp hMax.1 hm (hHead g hm) (head g hm).counts.2.2.2.1 F
    exact ⟨a,b,c,d⟩
  refine ⟨⟨fun g hm => (facts g hm).1,fun g hm => (facts g hm).2.1,
    fun g hm => (facts g hm).2.2.1,fun hB g hm => (facts g hm).2.2.2 hB⟩,?_⟩
  intro credits g hm
  obtain ⟨Y,hY,hT,hO,start,J,hOrd,F⟩ := lane g hm
  have hCredits : Protocol.Statistics.TerminalCorrectionCredits l X (g/l.block)
      (stageOf (warpOf l g)) visit := by rw [hm.2.1,hm.stage]; exact credits
  obtain ⟨pos,hPos,hNext⟩ := plainLaneNext hp hMax hY hT hO (frame X hMax.1) hm.1 hm.warp
    (head g hm) (H g hm).1 rfl hPlain hLt hTrips hSplitLe J hOrd hCredits
  exact ⟨pos,hNext,(outputsOfJoin hp hMax.1 hm (hHead g hm) (head g hm).counts.2.2.2.1
    F).2.2.2.2 pos hPos.le⟩

end PTX.Kernels.TmlFa4Fwd.Progress
