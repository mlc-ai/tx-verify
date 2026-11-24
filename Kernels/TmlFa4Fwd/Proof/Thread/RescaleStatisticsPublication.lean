-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxStats
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Lemmas.Order.Order
import Lemmas.Flow.NthEv
import Lemmas.Flow.CountTake
import Lemmas.Flow.WriteBytes
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Softmax

/-- The rescale publication uses the biased or plain repeated round. -/
def rescalePublication (biased : Bool) : Round := if biased then .biased else .plain

private def writeSite (biased : Bool) : Nat := (statsStore (rescaleStore biased)).pc

private def publishSite (biased : Bool) : Nat := writeSite biased + 1

private theorem publishCode (biased : Bool) :
    kernel.code[publishSite biased]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩ := by
  cases biased
  · exact Flow.code_6891
  · exact Flow.code_5683

private theorem publishOfNotice (biased : Bool) {e : Event}
    (h : notice e = some (rescalePublication biased)) : e.pc = publishSite biased := by
  cases biased <;> simp only [notice,rescalePublication,Bool.false_eq_true,↓reduceIte] at h
  all_goals
    split at h <;> try contradiction
    unfold noticeRound at h
    split at h <;> simp_all [publishSite,writeSite,rescaleStore,statsStore]

private def avoidsPublish (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
  match i.op with
  | .bra dst _ => !(dst == publishSite false || dst == publishSite true)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem avoidsPublishAudit : kernel.code.all avoidsPublish = true := by kernel_rfl

private theorem segmentAvoidsPublish {pc : Nat} {m : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some m)
    (biased : Bool) : m.stop ≠ publishSite biased := by
  have hAll : Assumptions.swExp2Sites.all (fun origin =>
    match cuteExp2.matchAt kernel origin with
    | none => false
    | some part => !(part.stop == publishSite false || part.stop == publishSite true)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll _ hSite
  rw [hm] at h
  have hBoth : m.stop ≠ publishSite false ∧ m.stop ≠ publishSite true := by simpa using h
  cases biased
  · exact hBoth.1
  · exact hBoth.2

private theorem noWriteTau {l : Launch} {g : Nat} {s u : TState} (biased : Bool)
    (hs : s.pc = writeSite biased) (ht : Tau kernel Assumptions.all l g s u) : False := by
  obtain ⟨i,hc,_,h⟩ := tauScoreSource ht
  cases biased
  · change s.pc = 6890 at hs
    rw [hs,Flow.code_6890] at hc
    obtain rfl := Option.some.inj hc
    rcases h with ⟨_,hn⟩ | ⟨_,hn,_⟩ <;> cases hn
  · change s.pc = 5682 at hs
    rw [hs,Flow.code_5682] at hc
    obtain rfl := Option.some.inj hc
    rcases h with ⟨_,hn⟩ | ⟨_,hn,_⟩ <;> cases hn

private theorem noPublishTau {l : Launch} {g : Nat} {s u : TState} (biased : Bool)
    (ht : Tau kernel Assumptions.all l g s u) (hu : u.pc = publishSite biased) : False := by
  obtain ⟨i,hc,_,h⟩ := tauScoreSource ht
  have step (hn : u.pc = s.pc+1) : False := by
    have hs : s.pc = writeSite biased := by unfold publishSite at hu; omega
    exact noWriteTau biased hs ht
  rcases h with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
  · exact step rfl
  rcases scoreExecLocal hLocal with hFrame | ⟨mat,hSeg,hMatch,hRun⟩
  · have hAudit := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp avoidsPublishAudit _ (List.mem_of_getElem? hc))).2
    have hp := hFrame.pc
    cases ho : i.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hp
    case bra dest uni =>
      have hn : dest = publishSite biased := hp.symm.trans hu
      subst dest
      simp [ho] at hAudit
      cases biased
      · exact hAudit.1 hn
      · exact hAudit.2 hn
    case brx => simp [ho] at hAudit
    all_goals exact step hp
  · exact segmentAvoidsPublish hSeg hMatch biased ((scoreSegmentFrame hRun).1.symm.trans hu)

private theorem writeKind {l : Launch} {g : Nat} {s u : TState} {e : Event} (biased : Bool)
    (hs : s.pc = writeSite biased) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ a bytes, e.kind = .wr a bytes ∧ bytes.length = a.size := by
  have write {base src : Nat}
      (hf : Fires s.pc (storeTmpl l g s .shared 32 base 368 [.reg src]) e (some u)) :
      ∃ a bytes, e.kind = .wr a bytes := by
    unfold storeTmpl at hf
    repeat' split at hf
    all_goals first | exact ⟨_,_,congrArg Event.kind hf.1⟩ | cases hf.2
  obtain ⟨i,hc,_,hf⟩ := estep_event_source he
  cases biased
  · change s.pc = 6890 at hs
    rw [hs,Flow.code_6890] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨a,bytes,hKind⟩ := write (base := 5518) (src := 1492) hf
    exact ⟨a,bytes,hKind,fires_write_length hf hKind rfl⟩
  · change s.pc = 5682 at hs
    rw [hs,Flow.code_5682] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨a,bytes,hKind⟩ := write (base := 4571) (src := 1362) hf
    exact ⟨a,bytes,hKind,fires_write_length hf hKind rfl⟩

private theorem writeBeforePublish {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (biased : Bool) (he : EStep kernel Assumptions.all l g s e (some u))
    (hu : u.pc = publishSite biased) :
    ∃ a bytes, e = ⟨writeSite biased,.wr a bytes⟩ ∧ bytes.length = a.size := by
  obtain ⟨i,hc,hL,hFire⟩ := estep_event_source he
  have hOrd := (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp avoidsPublishAudit _ (List.mem_of_getElem? hc))).1
  simp only [hL,Bool.false_or] at hOrd
  have ht : u.pc = s.pc + 1 := by
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrd) hFire with h | h
    · have hs : s.pc = publishSite biased := h.symm.trans hu
      have hp := followsMarkedBarrier hs (publishCode biased) rfl he
      omega
    · exact h
  have hs : s.pc = writeSite biased := by unfold publishSite at hu; omega
  obtain ⟨a,bytes,hKind,hLen⟩ := writeKind biased hs he
  have hSite := (estep_source_pc he).trans hs
  exact ⟨a,bytes,by cases e; congr,hLen⟩

private def WrittenBeforePublish (biased : Bool) (events : List Event) (s : TState) : Prop :=
  s.pc = publishSite biased → ∃ pre a bytes,
    events = pre ++ [⟨writeSite biased,.wr a bytes⟩] ∧ bytes.length = a.size

private theorem writtenOnReach {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (biased : Bool) (hr : TraceReach kernel Assumptions.all l g s events u) (seen : List Event)
    (hSeen : WrittenBeforePublish biased seen s) :
    WrittenBeforePublish biased (seen++events) u := by
  induction hr generalizing seen with
  | refl => simpa using hSeen
  | tau ht _ ih => exact ih seen (fun hs => (noPublishTau biased ht hs).elim)
  | @event s v u es e he _ ih =>
    rw [show e :: es = [e] ++ es by rfl,← List.append_assoc]
    apply ih (seen++[e])
    intro h
    obtain ⟨a,bytes,rfl,hLen⟩ := writeBeforePublish biased he h
    exact ⟨seen,a,bytes,rfl,hLen⟩

/-- Each actual repeated publication immediately follows the same lane's rescale word store. -/
theorem rescaleStoreBeforePublication {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g publication : Nat} (biased : Bool)
    (hPub : Publishes X (g,publication) (rescalePublication biased)) :
    ∃ write a bytes, write + 1 = publication ∧
      StatisticsStore X (g,write) (rescaleStore biased) a bytes ∧ bytes.length = a.size := by
  obtain ⟨e,he,hNotice⟩ := hPub
  obtain ⟨_,hr⟩ := hX.thr _ (event_thread_lt hX he)
  obtain ⟨s,_,hReach,hStep⟩ := hr.before_event he
  have hs := (estep_source_pc hStep).symm.trans (publishOfNotice biased hNotice)
  obtain ⟨pre,a,bytes,hList,hWidth⟩ := writtenOnReach biased hReach []
    (by intro h; cases biased <;> contradiction) hs
  simp only [List.nil_append] at hList
  have hLen := len_of_get he
  have hFirst := congrArg List.length hList
  simp only [List.length_take,List.length_append,List.length_cons,List.length_nil,
    Nat.min_eq_left hLen.le] at hFirst
  refine ⟨pre.length,a,bytes,by omega,?_,hWidth⟩
  change (X.tr g)[pre.length]? = _
  rw [← List.getElem?_take_of_lt (by omega : pre.length < publication),hList,
    List.getElem?_append_right (by rfl),Nat.sub_self]
  rfl

/-- The adjacent rescale store and its publication have the same notice ordinal. -/
theorem storeNoticeOfAdjacentPublication {X : Execution} {g writer publication : Nat}
    {site : Fin 4} {a : Acc} {bytes : List Byte}
    (hStore : StatisticsStore X (g,writer) site a bytes) (hNext : writer + 1 = publication) :
    (before X (g,writer)).notices = (before X (g,publication)).notices := by
  have h := countP_take_succ_false hStore
    (show publishesStats ⟨(statsStore site).pc,.wr a bytes⟩ = false by rfl)
  rw [beforeNotices,beforeNotices,← hNext,h]

/-- A store with no later notice ordinal than the publication lies before that publication. -/
theorem storeBeforePublicationOfNotice {X : Execution} {g writer publication : Nat}
    {site : Fin 4} {round : Round} {a : Acc} {bytes : List Byte}
    (hStore : StatisticsStore X (g,writer) site a bytes) (hPub : Publishes X (g,publication) round)
    (hOrd : (before X (g,writer)).notices ≤ (before X (g,publication)).notices) :
    writer < publication := by
  obtain ⟨e,he,hNotice⟩ := hPub
  rcases Nat.lt_trichotomy writer publication with h | rfl | h
  · exact h
  · obtain rfl := Option.some.inj (he.symm.trans hStore)
    cases hNotice
  · have hm : publishesStats e = true := by simp [publishesStats,hNotice]
    have hNext := countP_take_succ he hm
    have hLe := countP_take_mono publishesStats (X.tr g)
      (show publication+1 ≤ writer by omega)
    rw [beforeNotices,beforeNotices] at hOrd
    change ((X.tr g).take writer).countP _ ≤ ((X.tr g).take publication).countP _ at hOrd
    omega

/-- Two covering writes in the same softmax lane obey the lane's trace order. -/
theorem overlappingStoreBefore {l : Launch} {X : Execution}
    {g first second : Nat} {a b : Acc} {bytes data : List Byte} {loc : Loc}
    (hFirst : X.Writes (g,first) a bytes) (hSecond : X.Writes (g,second) b data)
    (hBefore : first < second) (ha : a.Covers loc) (hb : b.Covers loc) :
    baseCausality l X (g,first) (g,second) := by
  obtain ⟨_,hf⟩ := hFirst
  obtain ⟨_,hs⟩ := hSecond
  refine Relation.TransGen.single (.inl ⟨rfl,hBefore,len_of_get hs,?_⟩)
  intro hShuffle
  have hA : (X.get (g,first)).bind Event.acc = some a := by rw [hf]; rfl
  have hB : (X.get (g,second)).bind Event.acc = some b := by rw [hs]; rfl
  exact hShuffle.not_overlap rfl hBefore hA hB ⟨loc,ha,hb⟩

private theorem stateAfterRescaleWrite {l : Launch} {g : Nat} {s u : TState}
    (biased : Bool) {a : Acc} {bytes : List Byte}
    (hStep : EStep kernel Assumptions.all l g s ⟨writeSite biased,.wr a bytes⟩ (some u)) :
    u.pc = publishSite biased := by
  have hSite := (estep_source_pc hStep).symm
  have advances {base src : Nat}
      (hFire : Fires s.pc (storeTmpl l g s .shared 32 base 368 [.reg src])
        ⟨writeSite biased,.wr a bytes⟩ (some u)) : u.pc = s.pc+1 := by
    unfold storeTmpl at hFire
    repeat' split at hFire
    all_goals first | exact congrArg TState.pc (Option.some.inj hFire.2) | cases hFire.2
  obtain ⟨i,hCode,_,hFire⟩ := estep_event_source hStep
  have hNext : u.pc = s.pc + 1 := by
    cases biased
    · change s.pc = 6890 at hSite
      rw [hSite,Flow.code_6890] at hCode
      obtain rfl := Option.some.inj hCode
      exact advances (base := 5518) (src := 1492) hFire
    · change s.pc = 5682 at hSite
      rw [hSite,Flow.code_5682] at hCode
      obtain rfl := Option.some.inj hCode
      exact advances (base := 4571) (src := 1362) hFire
  rw [hNext,hSite]
  rfl

private theorem returningRescalePublication {l : Launch} {g : Nat} {s u : TState}
    (biased : Bool) {e : Event} (hSite : s.pc = publishSite biased)
    (hStep : EStep kernel Assumptions.all l g s e (some u)) :
    notice e = some (rescalePublication biased) := by
  obtain ⟨i,hCode,_,hFire⟩ := estep_event_source hStep
  rw [hSite,publishCode] at hCode
  obtain rfl := Option.some.inj hCode
  have hKind : ∃ id count, e.kind = .bar id count .arrive := by
    simp only [eventTmpl] at hFire
    unfold barTmpl at hFire
    repeat' split at hFire
    all_goals first | exact ⟨_,_,congrArg Event.kind hFire.1⟩ | cases hFire.2
  obtain ⟨id,count,hKind⟩ := hKind
  have hPc := (estep_source_pc hStep).trans hSite
  unfold notice
  rw [hKind,hPc]
  cases biased <;> rfl

private theorem publicationIsStop {l : Launch} {g : Nat} {s u : TState}
    (biased : Bool) (hSite : s.pc = publishSite biased)
    (hLocal : Tau kernel Assumptions.all l g s u) : False := by
  obtain ⟨i,hCode,_,hSkip | hExec⟩ := tauScoreSource hLocal
  all_goals
    rw [hSite,publishCode] at hCode
    obtain rfl := Option.some.inj hCode
    first | cases hSkip.2 | cases hExec.2.1

variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
include hX

private theorem rescaleWriteNoticeStrict {g first second : Nat} {biased later : Bool} {a b : Acc}
    {bytes data : List Byte} (hFirst : StatisticsStore X (g,first) (rescaleStore biased) a bytes)
    (hSecond : StatisticsStore X (g,second) (rescaleStore later) b data) (hOrder : first < second) :
    (before X (g,first)).notices < (before X (g,second)).notices := by
  have hSize : second < (X.tr g).length := len_of_get hSecond
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX hSecond)
  obtain ⟨s,u,hStep,hTail⟩ := hr.after_event hFirst (by omega)
  have hPc := stateAfterRescaleWrite biased hStep
  have hDifferent : ∀ b b', publishSite b ≠ writeSite b' := by decide
  have hReturn : ∃ e, X.get (g,first+1) = some e ∧
      notice e = some (rescalePublication biased) ∧ first+1 < second := by
    change Run kernel Assumptions.all l g u ((X.tr g).drop (first+1)) _ at hTail
    generalize hDrop : (X.tr g).drop (first+1) = suffix at hTail
    cases hTail with
    | nil =>
      have hLength := List.drop_eq_nil_iff.mp hDrop
      omega
    | @step _ t v e es o hLocal he hAfter =>
      have hState : u = t := by
        induction hLocal using Relation.ReflTransGen.head_induction_on with
        | refl => rfl
        | head h _ _ => exact (publicationIsStop biased hPc h).elim
      subst t
      have hGet : X.get (g,first+1) = some e := by
        change (X.tr g)[first+1]? = _
        have hFirst := congrArg (fun events : List Event => events[0]?) hDrop
        simpa only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] using hFirst
      have hLt : first+1 < second := by
        by_contra! hLe
        have hSame : first+1 = second := by omega
        rw [hSame] at hGet
        have hDiff := congrArg Event.pc (Option.some.inj (hGet.symm.trans hSecond))
        have hTag := (estep_source_pc he).trans hPc
        rw [hTag] at hDiff
        exact hDifferent biased later hDiff
      exact ⟨e,hGet,returningRescalePublication biased hPc he,hLt⟩
    | @last _ t e hLocal he =>
      have hState : u = t := by
        induction hLocal using Relation.ReflTransGen.head_induction_on with
        | refl => rfl
        | head h _ _ => exact (publicationIsStop biased hPc h).elim
      subst t
      have hLengths := congrArg List.length hDrop
      rw [List.length_drop] at hLengths
      have hSame : first+1 = second := by simp at hLengths; omega
      have hGet : X.get (g,first+1) = some e := by
        change (X.tr g)[first+1]? = _
        have hFirst := congrArg (fun events : List Event => events[0]?) hDrop
        simpa only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] using hFirst
      rw [hSame] at hGet
      have hDiff := congrArg Event.pc (Option.some.inj (hGet.symm.trans hSecond))
      rw [(estep_source_pc he).trans hPc] at hDiff
      exact (hDifferent biased later hDiff).elim
  obtain ⟨e,he,hPublication,hBefore⟩ := hReturn
  have hNext := countP_take_succ he (p := publishesStats) (by simp [publishesStats,hPublication])
  have hCount := countP_take_mono publishesStats (X.tr g)
    (show first+2 ≤ second by omega)
  change ((X.tr g).take (first+2)).countP publishesStats =
    ((X.tr g).take (first+1)).countP publishesStats+1 at hNext
  have hSame := storeNoticeOfAdjacentPublication hFirst (show first+1 = first+1 from rfl)
  rw [beforeNotices,beforeNotices] at hSame ⊢
  change ((X.tr g).take first).countP publishesStats =
    ((X.tr g).take (first+1)).countP publishesStats at hSame
  change ((X.tr g).take first).countP publishesStats <
    ((X.tr g).take second).countP publishesStats
  omega

/-- One softmax lane can publish at most one rescale word per notice ordinal.
Both arithmetic branches share the same ordinal. -/
theorem rescaleStoreUniqueOfNotice {g first second : Nat} {biased later : Bool} {a b : Acc}
    {bytes data : List Byte} (hFirst : StatisticsStore X (g,first) (rescaleStore biased) a bytes)
    (hSecond : StatisticsStore X (g,second) (rescaleStore later) b data)
    (hOrdinal : (before X (g,first)).notices = (before X (g,second)).notices) :
    first = second ∧ data = bytes := by
  have hSame : first = second := by
    rcases lt_trichotomy first second with h | h | h
    · exact ((rescaleWriteNoticeStrict hX hFirst hSecond h).ne hOrdinal).elim
    · exact h
    · exact ((rescaleWriteNoticeStrict hX hSecond hFirst h).ne hOrdinal.symm).elim
  subst second
  exact ⟨rfl,(Kind.wr.inj (Event.mk.inj (Option.some.inj
    (hSecond.symm.trans hFirst))).2).2⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
