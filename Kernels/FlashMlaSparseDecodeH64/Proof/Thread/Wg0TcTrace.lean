-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcPrologueRank
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcRank
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcSchedule
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

public section

/-! # Actual collective prefixes of the softmax lanes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcTrace

open PTX PTX.Flow TcCollectiveSites

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem data_isSome {s : Wg0.Site} : (dataOperands s).isSome = true ↔ DataSite s := by
  constructor
  · intro h
    cases s <;> simp only [dataOperands, Option.isSome, Bool.false_eq_true] at h
    all_goals constructor
  · intro h
    cases h <;> rfl

private theorem member_on_next {e : Event} {d d' : Wg0.D} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hn : Wg0.next P L g d e = some (some d')) :
    isTcColl e = (dataOperands d.site).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [data_isSome]
  constructor
  · intro he
    rcases TcCollectiveSites.of_fired hpre hf he with ⟨q, hq, hs⟩ | ⟨_, _, _, hk, hr⟩
    · cases hq
      exact hs
    · cases hr
      have hsite : d.site = .exit := by assumption
      simp [Wg0.next, Wg0.nextSite, hsite, hk] at hn
  · intro hs
    generalize hsite : d.site = s at hs
    cases hs <;> simp only [Wg0.next, Wg0.nextSite, hsite] at hn
    all_goals split at hn
    all_goals try contradiction
    all_goals
      cases e
      simp_all [isTcColl]

private theorem initial_rank (vote : Nat → Bool) :
    Wg0TcRank.Scheduled vote (Wg0.init P L g) ∧ Wg0TcRank.rank vote (Wg0.init P L g) = 0 := by
  unfold Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  split_ifs <;> simp [Wg0TcRank.Scheduled, Wg0VoteCount.afterVote, Wg0TcRank.rank,
    Wg0TcRank.blockOffset, Wg0TcRank.pastRescale, Wg0TcRank.priorRescales, Wg0.Site.inRescale]

private def Counts (L : Launch) (X : Execution) (g : Nat) :
    Option Machine.ThreadD → List Event → Prop
  | some (.prologue s), es =>
    TcPrologueRank.InScope L g s ∧ es.countP isTcColl = TcPrologueRank.rank L g s
  | some (.wg0 d), es =>
    Wg0TcRank.Scheduled (Wg0TcSchedule.voteOf L X g) d ∧
    es.countP isTcColl = TcPrologueRank.setup L g + Wg0TcRank.rank (Wg0TcSchedule.voteOf L X g) d
  | _, _ => True

private theorem cast_vote {d : Wg0.D} {e : Event} {o : Option TState} {i : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    {mode : VoteMode} {mask : Nat} {p result : Bool}
    (hk : e.kind = .voteMode mode mask p result) :
    result = Wg0TcSchedule.voteOf L X g d.block := by
  have hcls : voteClass e.kind ≠ none := by simp [hk, voteClass]
  obtain ⟨q, r, hq, hsite, hr⟩ := Wg0VoteSites.of_fired hf hcls
  cases hq
  have hsKind := Kind.voteMode.inj (hk.symm.trans hr)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hsKind
  have he' : X.get (g, i) = some ⟨e.pc, .voteMode .any (2 ^ 32 - 1) d.voteTest result⟩ := by
    cases e
    exact he.trans (congrArg some (congrArg (Event.mk _) hr))
  exact Wg0TcSchedule.at_vote hX hs he' hd hsite

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
include hpre hX hs

private theorem counts_next {d d' : Option Machine.ThreadD} {i : Nat} {e : Event}
    {o : Option TState} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some d) (hc : Counts L X g d ((X.tr g).take i))
    (hf : (Machine.machine P L g).Fired d e o) (hn : (Machine.machine P L g).next d e = some d') :
    Counts L X g d' (((X.tr g).take i) ++ [e]) := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      obtain ⟨hscope, hrank⟩ := hc
      simp only [Machine.next] at hn
      split at hn
      · rename_i s' hStep
        cases hn
        obtain ⟨hscope', hStep'⟩ := TcPrologueRank.step hpre hf hscope hStep
        exact ⟨hscope', by simp [List.countP_append, hrank, hStep', Bool.toNat]⟩
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn
            · change TcPrologueRank.InScope L g (.handoff 0) at hscope
              have hnond : isTcColl e = false := by
                cases hk : isTcColl e
                · rfl
                rcases TcCollectiveSites.of_fired hpre hf hk with ⟨_, hi, _⟩ | ⟨_, _, _, _, hi⟩
                · cases hi
                · cases hi
              obtain ⟨ha, hb⟩ := initial_rank (P := P) (L := L) (g := g)
                (Wg0TcSchedule.voteOf L X g)
              exact ⟨ha, by simp [List.countP_append, hrank, TcPrologueRank.rank, hnond, hb]⟩
            · trivial
            · trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> trivial
    case wg0 d =>
      obtain ⟨hScheduled, hCount⟩ := hc
      simp only [Machine.next] at hn
      split at hn
      · rename_i q hStep
        cases hn
        have hInv : Wg0.Inv P L g d := (Exists.choose_spec hf).1.2
        have h := Wg0TcRank.step hScheduled hInv.rescaleArm hStep
          (fun _ _ _ _ => cast_vote hX hs he hd hf)
        obtain ⟨hScheduled', hr⟩ := h
        have hb := member_on_next hpre hf hStep
        exact ⟨hScheduled', by simp [List.countP_append, hCount, hr, hb, Bool.toNat, Nat.add_assoc]⟩
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    all_goals
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial

private theorem counts_at (hg : g < L.threads) {i : Nat} {state : Option Machine.ThreadD}
    (hi : i ≤ (X.tr g).length) (hd : Frame.stateAt (Machine.code P L) X g i = some state) :
    Counts L X g state ((X.tr g).take i) := by
  have ht := hs.produces (hX.thr g hg)
  have all (i : Nat) (hi : i ≤ (X.tr g).length) (s : Option Machine.ThreadD)
      (hd : Frame.stateAt (Machine.code P L) X g i = some s) :
      Counts L X g s ((X.tr g).take i) := by
    induction i generalizing s with
    | zero =>
      change some (some (.prologue .shfl0)) = some s at hd
      cases hd
      exact ⟨trivial, rfl⟩
    | succ i ih =>
      have hj : i < (X.tr g).length := by omega
      let e := (X.tr g)[i]
      have he : X.get (g, i) = some e := List.getElem?_eq_getElem hj
      rw [Frame.stateAt_succ he] at hd
      cases hstate : Frame.stateAt (Machine.code P L) X g i with
      | none => rw [hstate] at hd; cases hd
      | some old =>
        rw [hstate] at hd
        have hn : (Machine.machine P L g).next old e = some s := hd
        have hc := ih (by omega) old hstate
        obtain ⟨o, hf⟩ := ht.fired_at he hstate
        have h := counts_next hpre hX hs he hstate hc hf hn
        simpa only [List.take_add_one, show (X.tr g)[i]? = some e from he,
          Option.toList_some] using h
  exact all i hi _ hd

/-- The actual prefix reaching a softmax site has its scheduled Tensor Memory ordinal. -/
theorem rank_at (hg : g < L.threads) {i : Nat} {d : Wg0.D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) :
    Wg0TcRank.Scheduled (Wg0TcSchedule.voteOf L X g) d ∧
      ((X.tr g).take i).countP isTcColl =
        TcPrologueRank.setup L g + Wg0TcRank.rank (Wg0TcSchedule.voteOf L X g) d :=
  counts_at hpre hX hs hg hi hd

/-- The prefix at an actual prologue state has its allocator collective ordinal. -/
theorem prologue_rank_at (hg : g < L.threads) {i : Nat} {s : Proof.Site} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue s))) :
    TcPrologueRank.InScope L g s ∧
      ((X.tr g).take i).countP isTcColl = TcPrologueRank.rank L g s :=
  counts_at hpre hX hs hg hi hd

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcTrace
