-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Kernel.Existence
public import Lemmas.Execution.NoAsync
public import Tests.Async.AsyncExecution
public import Lemmas.Order.Order
public import Lemmas.Order.OrderNotAccess
import Lemmas.Tmem.AllocResult

/-!
# Semantic regression checks

Thread program order does not publish unrelated async effects. These checks cover unsynchronized
conflicts, barrier publication, independent copy completion, waits on another object or phase, and a
local infinite loop. None uses a synthetic thread write to stand for completion of an asynchronous
copy. -/
namespace PTX
noncomputable section
open AsyncCopy

/-- The linear copy of `src` to `dst` that completes on mbarrier `m` (`cp.async.bulk`). -/
def mbarCopy (src dst : Acc) (m : Loc) : Spec :=
  { src := src, dst := dst, completion := .mbarrier m }

/-- `fence.proxy.async.shared::cta`. -/
local notation "fenceAsync" =>
  Kind.fenceProxy (ProxyFence.async (some (StateSpace.shared SharedWindow.cta))) none

/-- The effects of a completed whole copy of `p`: it read and wrote `p` and notified. -/
def done (p : List Byte) : Effects :=
  { readBytes := some p, writeBytes := some p, notified := true }

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

theorem race_of_noBar (hnb : ∀ e k, ¬ CtaBarK L X e k) (hnw : ∀ w m, ¬ X.AcquireWait w m)
    (hnc : ∀ e f, ¬ ClusterSync L X e f)
    (hnwb : ∀ e f, ¬ WarpBarSync L X e f) (hnac : ∀ e f, ¬ synchronizesWith L X e f)
    (hnf : ∀ e f, ¬ FenceSync L X e f)
    (hnm : ∀ i d s accum mask, ¬ X.MmaIssue i d s accum mask)
    (hncP : ∀ i c, ¬ X.CpIssue i c)
    {w r : EvId} {a : Acc} {bs : List Byte} (hw : X.Writes w a bs)
    {b : Bool} (hr : X.Access r a b) (hne : w.1 ≠ r.1) (ha : 0 < a.size)
    (haWr : ¬ Tmem.Pair.AllocResultBefore L X (a.loc.at 0) w r)
    (haRd : ¬ Tmem.Pair.AllocResultBefore L X (a.loc.at 0) r w)
    (hweak : ¬ a.Strong) (hdiff : ¬ SameValueWrites X (.thread w) (.thread r) a a) :
    Race L X := by
  have hsame : ∀ {e f : EvId}, baseCausality L X e f → e.1 = f.1 := fun h =>
    (baseCausality_of_noBar hnb hnw hnc hnwb hnac hnf h).1
  refine ⟨.thread w, .thread r, a, a, a.loc.at 0, ?_, ⟨rfl,rfl⟩, Acc.covers_at ha, ?_,
    fun h => ((ByteCausality.direct_iff_of_no_operand hnm hncP).1 h).elim
      (fun hb => hne (hsame hb)) haWr,
    fun h => ((ByteCausality.direct_iff_of_no_operand hnm hncP).1 h).elim
      (fun hb => hne (hsame hb).symm) haRd, hdiff⟩
  · exact ⟨fun hh => hne (congrArg Prod.fst (Ref.thread.inj hh)), true, b,
      hw.access, hr, .inl rfl, a.loc.at 0, Acc.covers_at ha, Acc.covers_at ha⟩
  · rintro ⟨⟨i, j, hi, hj, hij⟩ | ⟨⟨-, hs, -⟩, -⟩, -, -⟩
    · cases hi; cases hj; exact hne hij
    · exact hweak hs

theorem bar_baseCausality {g h i j k i' j' : Nat} (hs : SameCta L g h) (hi : CtaBarK L X (g, i) k)
    (hj : CtaBarK L X (h, j) k) (hi' : i' < i) (hj' : j < j') (hl : j' < (X.tr h).length) :
    baseCausality L X (g, i') (h, j') :=
  .single (.inr (.inl ⟨hs, k, i, j, ⟨hi.1, (let ⟨c, pc, h⟩ := hi.2.1; ⟨c, pc, _, h⟩), hi.2.2⟩, hj,
    hi', hj', hl⟩))

/-- Writer uniqueness is this theorem's sufficient premise, not a Core restriction. -/
theorem bar_value (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X) (hr : ¬ Race L X)
    (hs : StrongOrdered L X)
    {e : EvId} {a : Acc} {bs : List (Option Byte)} (he : X.Reads e a bs) {k : Nat}
    (hk : k < a.size) {w : EvId} {a' : Acc} {bs' : List Byte} (hw : X.Writes w a' bs')
    (hc : a'.Covers (a.loc.at k)) (hwe : baseCausality L X w e)
    (huniq : ∀ w' a'' bs'', X.MemWrites w' a'' bs'' → a''.Covers (a.loc.at k) → w' = .thread w) :
    bs[k]? = some (wbyte a' bs' (a.loc.at k)) :=
  read_byte_of_latest hX hm hr hs (e := .thread e) (w := .thread w) (Or.inl he) hk
    (by
      rintro i acc old new ⟨hi, ⟨pc, h1⟩⟩
      obtain ⟨pc', h2⟩ := he
      cases hi
      rw [h1] at h2; cases h2)
    (Or.inl hw) hc (.inl hwe)
    (fun w' a'' bs'' hw' hc' _ => Or.inl (huniq w' a'' bs'' hw' hc'))

/-- An independent destination conflicts with an unordered reader, including before
its write effect exists. The reverse proxy-publication path is checked as well. -/
theorem copy_unwaited {c e : EvId} {s d : Acc} {m l : Loc} {bs : List (Option Byte)}
    (hc : X.Copy c (mbarCopy s d m)) (he : X.Reads e d bs) (hl : d.Covers l)
    (hnm : ∀ i d s accum mask, ¬ X.MmaIssue i d s accum mask)
    (hncP : ∀ i c, ¬ X.CpIssue i c)
    (hno : ¬ ∃ w, AsyncFinished L X c (.write .copy) w ∧
      baseCausality L X w e) (hback : ¬ ProxyBefore L X e c l) : Race L X := by
  refine ⟨.async c (.write .copy), .thread e, d, d, l, ?_, ⟨rfl,rfl⟩, hl, ?_, ?_, ?_, ?_⟩
  · exact ⟨(by intro h; cases h), true, false, ⟨rfl, ⟨mbarCopy s d m, hc, rfl, rfl⟩⟩,
      he.access, Or.inl rfl, l, hl, hl⟩
  · rintro ⟨⟨i, j, hi, -⟩ | ⟨h1, -⟩, -, -⟩
    · cases hi
    · exact not_strongScoped_write_copy L hc rfl h1
  · rw [ByteCausality.direct_iff_of_no_operand hnm hncP]
    rintro ⟨_, w, ho, hb⟩
    exact hno ⟨w, ho, by
      simpa only [ObservedCompletionBefore, CompletionBefore, TcReadReuseBefore, or_false]
        using hb⟩
  · rw [ByteCausality.direct_iff_of_no_operand hnm hncP]
    intro h
    rcases h.2 with h | ⟨hg, -⟩
    · exact hback h
    · exact not_genericCopy_of_mbarrier hc rfl hg
  · rintro ⟨-, ⟨bs', -, hf⟩ | ⟨bs', hw', -⟩ | ⟨old, new, ⟨pc, hrm⟩⟩, -⟩
    · cases hf
    · exact Execution.Reads.ne_write he hw' rfl
    · obtain ⟨pc', hr⟩ := he
      rw [hr] at hrm; cases hrm
end

private def regressionLog (ops : List (Ref × MBarrier.Action)) : List (MBarrier.Record Ref) :=
  match MBarrier.replay none ops with
  | .ok xs => xs
  | .error _ => []

private def legacyKind : Kind → Bool
  | .mbInit .. | .fenceProxy .. | .bar .. | .arrive .. | .copy .. | .wait .. | .rd .. | .exit =>
    true
  | .wr a _ => !a.release
  | _ => false

private theorem baseCausality_legacy {L : Launch} {X : Execution}
    (hkind : ∀ e pc k, X.get e = some ⟨pc,k⟩ → legacyKind k = true)
    (hclusters : ∀ c, X.clusters c = []) {e f : EvId} (h : baseCausality L X e f) :
    Relation.TransGen (fun e f => po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f) e f := by
  have step : ∀e f, (po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨ ClusterSync L X e f ∨
      WarpBarSync L X e f ∨ synchronizesWith L X e f ∨ FenceSync L X e f) →
      po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f := by
    intro e f hh
    rcases hh with hh | hh | hh | hh | hh | hh | hh
    · exact .inl hh
    · exact .inr (.inl hh)
    · exact .inr (.inr hh)
    · obtain ⟨_,i,j,hs,_⟩ := hh
      obtain ⟨phase,ha,_⟩ := hs
      obtain ⟨idx,st,next,cta,warp,lanes,g,hi,_⟩ := ha
      simp [hclusters] at hi
    · obtain ⟨i,j,⟨_,mask,inst,⟨pc,hi⟩,_⟩,_⟩ := hh
      cases hkind _ _ _ hi
    · obtain ⟨a,b,bs,cs,hw,_,hr,_⟩ := hh
      rcases hw with ⟨pc,hi⟩ | ⟨old,pc,hi⟩
      · have hk := hkind _ _ _ hi
        simp [legacyKind,hr] at hk
      · have hk := hkind _ _ _ hi
        simp [legacyKind] at hk
    · rcases hh with ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,⟨sem,sc,⟨pc,hi⟩ | ⟨pc,hi⟩⟩,-⟩ |
        ⟨⟨sc,-,⟨pc,hi⟩,-⟩,-⟩
      all_goals exact absurd (hkind _ _ _ hi) (by simp [legacyKind])
  induction h with
  | single h => exact .single (step _ _ h)
  | tail _ h ih => exact ih.tail (step _ _ h)

namespace Tma
def launch : Launch := { grid := 1, block := 1, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def src : Acc := { loc := ⟨.global, 0, 0⟩, size := 16 }
def dst : Acc := { loc := ⟨.shared, 0, 0⟩, size := 16 }
def m1 : Loc := ⟨.shared, 0, 16⟩
def m2 : Loc := ⟨.shared, 0, 24⟩
def payload : List Byte := List.replicate 16 (.bits 32 0, 0)
def log1 := regressionLog [(.thread (0, 0), .init 1), (.thread (0, 3), .arrive 1 16),
  (.async (0, 4) (.notify .copy), .completeTx 16)]
def log2 := regressionLog [(.thread (0, 1), .init 1), (.thread (0, 5), .arrive 1 0),
  (.thread (0, 6), .pollParity 0 true)]
def ex : Execution where
  tr g := if g = 0 then [⟨0, .mbInit m1 1⟩, ⟨1, .mbInit m2 1⟩, ⟨2, fenceAsync⟩,
    ⟨3, .arrive m1 16⟩, ⟨4, .copy (mbarCopy src dst m1)⟩, ⟨5, .arrive m2 0⟩,
    ⟨6, .wait m2 0 true⟩, ⟨7, .rd dst (payload.map some)⟩, ⟨8, .exit⟩] else []
  rf _ _ := some (.async (0, 4) (.write .copy))
  async := { copies := fun i => if i = (0, 4) then done payload else {} }
  objects m := if m = m1 then log1 else if m = m2 then log2 else []

private theorem ex_legacy (e : EvId) (pc : Nat) (k : Kind)
    (h : ex.get e = some ⟨pc,k⟩) : legacyKind k = true := by
  have hm := List.mem_of_getElem? h
  simp only [ex] at hm
  split_ifs at hm <;> simp_all only [List.mem_cons,List.not_mem_nil,or_false,Event.mk.injEq]
  all_goals
    repeat' (rcases hm with hm | hm)
  all_goals simp_all [legacyKind]

theorem copy_event :
    ex.Copy (0, 4) (mbarCopy src dst m1) ∧ ∃ bs, (ex.async.copies (0, 4)).writeBytes = some bs :=
  ⟨⟨4, rfl⟩, payload, rfl⟩

-- Both objects have legal histories; waiting on the second does not observe the first.
example : MBarrier.CheckedLog log1 :=
  MBarrier.checkedLog_of_replay (ops := [(.thread (0, 0), .init 1), (.thread (0, 3), .arrive 1 16),
    (.async (0, 4) (.notify .copy), .completeTx 16)]) (by rfl) (by decide)
example : MBarrier.CheckedLog log2 :=
  MBarrier.checkedLog_of_replay (ops := [(.thread (0, 1), .init 1), (.thread (0, 5), .arrive 1 0),
    (.thread (0, 6), .pollParity 0 true)]) (by rfl) (by decide)

theorem copy_not_visible (f : EvId) :
    ¬ ∃ w, AsyncFinished launch ex (0, 4) (.write .copy) w ∧ baseCausality launch ex w f := by
  rintro ⟨w, hfin, -⟩
  rw [asyncFinished_copy_of_mbarrier launch (s := mbarCopy src dst m1) ⟨4, rfl⟩ rfl] at hfin
  obtain ⟨_, ⟨n, m, hn, -, i, j, r, wr, phase, _, _, _, hw, _, _, hwait, _⟩, -⟩ := hfin
  rw [notifies_copy_of_mbarrier (s := mbarCopy src dst m1) ⟨4, rfl⟩ rfl (Or.inr rfl)] at hn
  obtain ⟨-, -, s, hi, -, hm, -⟩ := hn
  have hs : s = mbarCopy src dst m1 := by simpa [issuedBy, Execution.get, ex] using hi.symm
  subst s
  have hm1 : m1 = m := by injection hm
  subst hm1
  have hwmem := List.mem_of_getElem? hw
  change wr ∈ [_, _, _] at hwmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwmem
  rcases hwmem with rfl | rfl | rfl <;> cases hwait

private theorem no_bar {e : EvId} {pc id : Nat} : ¬ ex.IsBarrier e id none pc := by
  intro he
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    have hm := List.mem_of_getElem? he
    simp [ex] at hm
  · simp [Execution.IsBarrier, Execution.get, ex, hg] at he

private theorem arrive_before {e : EvId} {m : Loc} {tx count : Nat} {rel : Bool} {sc : MbarScope}
    (he : ex.Arrive e m tx count rel sc) : e.2 ≤ 5 := by
  obtain ⟨g, i⟩ := e
  obtain ⟨pc, hp⟩ := he
  by_cases hg : g = 0
  · subst g
    have hil : i < 9 := (List.getElem?_eq_some_iff.mp hp).1
    interval_cases i <;> simp_all [Execution.get, ex]
    all_goals omega
  · simp [Execution.get, ex, hg] at hp

private theorem no_proxy : ¬ ProxyBefore launch ex (0, 7) (0, 4) dst.loc := by
  rintro ⟨⟨g, i⟩, _, _, ⟨pc, hf⟩, _, _, _, hbefore, -⟩
  by_cases hg : g = 0
  · subst g
    have hi : i = 2 := by
      have hil : i < 9 := (List.getElem?_eq_some_iff.mp hf).1
      interval_cases i <;> first | rfl | (change some _ = some _ at hf; cases hf)
    subst i
    have step : ∀ {e f}, (po ex e f ∨ CtaBarSync launch ex e f ∨ MSync launch ex e f) →
        7 ≤ e.2 → 7 ≤ f.2 := by
      intro e f h he
      rcases h with hp | hs | hm
      · have := hp.2.1; omega
      · obtain ⟨_,key,i,j,hi,_⟩ := hs
        obtain ⟨idx,st,warp,count,lanes,g,hget,_⟩ := hi.2.2
        simp [ex] at hget
      · obtain ⟨x, w, m, rs, ws, ha, -, -, -, -, -, -, hex⟩ := hm
        have := arrive_before ha.choose_spec.choose_spec
        omega
    have closed : ∀ {e f}, baseCausality launch ex e f → 7 ≤ e.2 → 7 ≤ f.2 := by
      intro e f h he
      have hlegacy := baseCausality_legacy ex_legacy (fun _ => rfl) h
      clear h
      induction hlegacy with
      | single hedge => exact step hedge he
      | tail _ hedge ih => exact step hedge ih
    have hh := closed hbefore (by decide)
    omega
  · simp [Execution.get, ex, hg] at hf

theorem unrelated_wait_unsafe (mem0 : Mem0) : Unsafe launch { name := "k", params := [], code :=
                                                              [] } [] mem0 ex :=
  .inr (.inr (.inl (copy_unwaited (c := (0, 4)) (e := (0, 7)) ⟨4, rfl⟩ ⟨7, rfl⟩
    (show dst.Covers dst.loc from ⟨rfl, rfl, by decide, by decide⟩)
    (by
      rintro i d s accum mask ⟨pc, h⟩
      have := ex_legacy i pc _ h
      simp [legacyKind] at this)
    (by
      rintro i c ⟨pc, h⟩
      have := ex_legacy i pc _ h
      simp [legacyKind] at this)
    (copy_not_visible _) no_proxy)))

def issuedOnly : Execution where
  tr g := (ex.tr g).take 5
  rf _ _ := none
  objects m := if m = m1 then regressionLog [(.thread (0, 0), .init 1),
    (.thread (0, 3), .arrive 1 16)] else []

theorem issued_not_complete (w : EvId) {acq : Bool} {ws : MbarScope} :
    ¬ AsyncObserved issuedOnly (0, 4) (.notify .copy) w acq ws := by
  rintro ⟨_, _, ⟨_, _, _, _, hn, _⟩, _⟩
  cases hn
end Tma

namespace TmaScope

def launch : Launch := { grid := 1, block := 2, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def src : Acc := { loc := ⟨.global, 0, 0⟩, size := 16 }
def dst : Acc := { loc := ⟨.shared, 0, 0⟩, size := 16 }
def mb : Loc := ⟨.shared, 0, 16⟩
def flag : Acc := { loc := ⟨.global, 0, 64⟩, size := 4 }
def payload : List Byte := List.replicate 16 (.bits 32 0, 0)

def pub (v : Value) : Execution where
  tr g := if g = 0 then [⟨0, .mbInit mb 1⟩, ⟨1, fenceAsync⟩, ⟨2, .bar 0⟩,
    ⟨3, .arrive mb 16⟩, ⟨4, .wr flag (Value.bits 32 1).toBytes⟩,
    ⟨5, .copy (mbarCopy src dst mb)⟩, ⟨6, .wait mb 0 true⟩, ⟨7, .exit⟩]
    else if g = 1 then [⟨2, .bar 0⟩, ⟨9, .wait mb 0 true⟩,
      ⟨10, .rd flag (v.toBytes.map some)⟩, ⟨11, .exit⟩] else []
  rf _ _ := none
  async := { copies := fun i => if i = (0, 5) then done payload else {} }
  objects m := if m = mb then regressionLog [(.thread (0, 0), .init 1),
    (.thread (0, 3), .arrive 1 16), (.async (0, 5) (.notify .copy), .completeTx 16),
    (.thread (0, 6), .pollParity 0 true), (.thread (1, 1), .pollParity 0 true)] else []

private theorem pub_legacy (v : Value) (e : EvId) (pc : Nat) (k : Kind)
    (h : (pub v).get e = some ⟨pc,k⟩) : legacyKind k = true := by
  have hm := List.mem_of_getElem? h
  simp only [pub] at hm
  split_ifs at hm <;> simp_all only [List.mem_cons,List.not_mem_nil,or_false,Event.mk.injEq]
  all_goals
    repeat' (rcases hm with hm | hm)
  all_goals simp_all [legacyKind,flag]

theorem pub_observed_by_reader (v : Value) :
    AsyncObserved (pub v) (0, 5) (.notify .copy) (1, 1) true .cta := by
  refine ⟨.async (0, 5) (.notify .copy), mb, ⟨rfl, 16, mbarCopy src dst mb, rfl, rfl, rfl, rfl⟩,
    ⟨⟨9, 0, rfl⟩, ?_⟩⟩
  refine ⟨2, 4, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
    fun k s h1 h2 hk ha => ?_⟩
  obtain rfl : k = 3 := by omega
  have h3 : ((pub v).objects mb)[3]?.map (·.action) = some .inval := by rw [hk]; simp [ha]
  have h4 : ((pub v).objects mb)[3]?.map (·.action) = (regressionLog [(.thread (0, 0), .init 1),
      (.thread (0, 3), .arrive 1 16), (.async (0, 5) (.notify .copy), .completeTx 16),
      (.thread (0, 6), .pollParity 0 true), (.thread (1, 1), .pollParity 0 true)])[3]?.map
      (·.action) := by simp [pub]
  rw [h4] at h3
  revert h3
  decide

theorem pub_bar {v : Value} {j id pc : Nat} (h : (pub v).IsBarrier (0, j) id none pc) : j = 2 := by
  unfold Execution.IsBarrier Execution.get at h
  simp only [pub] at h
  match j with
  | 0 | 1 | 3 | 4 | 5 | 6 | 7 | _ + 8 => simp at h
  | 2 => rfl

theorem pub_arrive {v : Value} {j : Nat} {m : Loc} {tx count : Nat} {rel : Bool} {sc : MbarScope}
    (h : (pub v).Arrive (0, j) m tx count rel sc) : j = 3 := by
  obtain ⟨pc, h⟩ := h
  unfold Execution.get at h
  simp only [pub] at h
  match j with
  | 0 | 1 | 2 | 4 | 5 | 6 | 7 | _ + 8 => simp at h
  | 3 => rfl

theorem pub_closed {v : Value} {e f : EvId} (h : baseCausality launch (pub v) e f)
    (he : e.1 = 0 ∧ 4 ≤ e.2) : f.1 = 0 ∧ 4 ≤ f.2 := by
  have step : ∀ {a b}, (po (pub v) a b ∨ CtaBarSync launch (pub v) a b ∨ MSync launch (pub v) a b) →
      a.1 = 0 ∧ 4 ≤ a.2 → b.1 = 0 ∧ 4 ≤ b.2 := by
    intro a b h ha
    rcases h with ⟨h1, h2, _⟩ | ⟨_, k, i, j, hi, _, hai, _⟩ |
      ⟨x, w, m, rs, ws, ⟨tx, count, harr⟩, -, -, -, -, -, hx, hle⟩
    · exact ⟨h1 ▸ ha.1, by omega⟩
    · obtain ⟨idx,st,warp,count,lanes,g,hget,_⟩ := hi.2.2
      simp [pub] at hget
    · have hx0 : x.1 = 0 := hx.trans ha.1
      have harr' : (pub v).Arrive (0, x.2) m tx count true rs := by simpa only [← hx0] using harr
      have := pub_arrive harr'; omega
  have hlegacy := baseCausality_legacy (pub_legacy v) (fun _ => rfl) h
  clear h
  induction hlegacy with
  | single hedge => exact step hedge he
  | tail _ hedge ih => exact step hedge ih

/-- Completion publishes this copy, not its issuer's store after the release arrival. -/
theorem store_not_visible (v : Value) : ¬ baseCausality launch (pub v) (0, 4) (1, 2) := by
  intro h
  have := (pub_closed h ⟨rfl, le_refl _⟩).1
  simp at this

private theorem pub_copy {v : Value} {i : EvId} {s : Spec} (h : (pub v).Copy i s) :
    i = (0, 5) ∧ s = mbarCopy src dst mb := by
  obtain ⟨g, i⟩ := i
  obtain ⟨pc, hp⟩ := h
  by_cases h0 : g = 0
  · subst g
    have hi : i < 8 := (List.getElem?_eq_some_iff.mp hp).1
    interval_cases i <;> simp [Execution.get, pub] at hp
    exact ⟨rfl, hp.2.symm⟩
  · by_cases h1 : g = 1
    · subst g
      have hi : i < 4 := (List.getElem?_eq_some_iff.mp hp).1
      interval_cases i <;> simp [Execution.get, pub] at hp
    · simp [Execution.get, pub, h0, h1] at hp

private theorem pub_not_rmw (v : Value) (e : EvId) (pc : Nat) (a : Acc) (o : List (Option Byte))
    (n : Option (List Byte)) : (pub v).get e ≠ some ⟨pc, .rmw a o n⟩ := fun h => by
  have := pub_legacy v e pc _ h
  simp [legacyKind] at this

private theorem pub_read_cases {v : Value} {e : Ref} {a : Acc} {bs : List (Option Byte)}
    (h : (pub v).MemReads e a bs) :
    (e = .thread (1, 2) ∧ a = flag) ∨ (e = .async (0, 5) (.read .copy) ∧ a = src) := by
  cases e with
  | thread e =>
    obtain ⟨pc, hp⟩ := (Execution.memReads_thread_iff_of_not_rmw (pub_not_rmw v e)).mp h
    obtain ⟨g, i⟩ := e
    by_cases h0 : g = 0
    · subst g
      have hi : i < 8 := (List.getElem?_eq_some_iff.mp hp).1
      interval_cases i <;> simp [Execution.get, pub] at hp
    · by_cases h1 : g = 1
      · subst g
        have hi : i < 4 := (List.getElem?_eq_some_iff.mp hp).1
        interval_cases i <;> simp [Execution.get, pub] at hp
        exact .inl ⟨rfl, hp.2.1.symm⟩
      · simp [Execution.get, pub, h0, h1] at hp
  | async i p =>
    cases p <;> simp only [Execution.MemReads] at h
    all_goals try solve | simp [Execution.MmaRead,pub] at h
    · obtain ⟨s, raw, hb, hs, -⟩ := h
      obtain ⟨rfl, rfl⟩ := pub_copy hb
      exact .inr ⟨rfl, hs.symm⟩
    · obtain ⟨s, r, raw, hb, hw, -⟩ := h
      obtain ⟨rfl, rfl⟩ := pub_copy hb
      cases hw

private theorem pub_write_cases {v : Value} {e : Ref} {a : Acc} {bs : List Byte}
    (h : (pub v).MemWrites e a bs) :
    (e = .thread (0, 4) ∧ a = flag) ∨ (e = .async (0, 5) (.write .copy) ∧ a = dst) := by
  cases e with
  | thread e =>
    obtain ⟨pc, hp⟩ := (Execution.memWrites_thread_iff_of_not_rmw (pub_not_rmw v e)).mp h
    obtain ⟨g, i⟩ := e
    by_cases h0 : g = 0
    · subst g
      have hi : i < 8 := (List.getElem?_eq_some_iff.mp hp).1
      interval_cases i <;> simp [Execution.get, pub] at hp
      exact .inl ⟨rfl, hp.2.1.symm⟩
    · by_cases h1 : g = 1
      · subst g
        have hi : i < 4 := (List.getElem?_eq_some_iff.mp hp).1
        interval_cases i <;> simp [Execution.get, pub] at hp
      · simp [Execution.get, pub, h0, h1] at hp
  | async i p =>
    cases p <;> simp only [Execution.MemWrites] at h
    all_goals try solve | simp [Clc.ResponseWrite,pub] at h
    · obtain ⟨s, hb, -, hd, -⟩ := h
      obtain ⟨rfl, rfl⟩ := pub_copy hb
      exact .inr ⟨rfl, hd.symm⟩
    · obtain ⟨s, hb, he, -⟩ := h
      obtain ⟨rfl, rfl⟩ := pub_copy hb
      simp [Spec.elems, Spec.elemOffsets, mbarCopy] at he

/-- W0 for flag satisfies Hidden even with the actual independent copy effects present. -/
theorem old_value_allowed : Hidden launch (pub (.bits 32 0)) := by
  intro e a bs k w a' bs' he hk hw hc hwe
  rcases pub_read_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases pub_write_cases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases (ByteCausality.direct_iff_of_global rfl).1 hwe with hb | ha
    · exact False.elim (store_not_visible _ hb)
    · cases ha.shared.1
  all_goals simp [Acc.Covers, Loc.InRange, Loc.at, flag, dst, src] at hc hk
  omega

-- A single successful wait can hand completion to another thread through bar.sync.
def fwdLog := regressionLog [(.thread (0, 0), .init 1), (.thread (0, 2), .arrive 1 16),
  (.async (0, 3) (.notify .copy), .completeTx 16), (.thread (0, 4), .pollParity 0 true)]
private def fwdLanes : List (Nat × EvId) := [(0,(0,6)),(1,(1,0))]
private def fwdState : CtaBarrier.State := {
  slots := fun id => if id = 0 then { generation := 1 } else {} }
def fwd : Execution where
  tr g := if g = 0 then [⟨0, .mbInit mb 1⟩, ⟨1, fenceAsync⟩, ⟨2, .arrive mb 16⟩,
    ⟨3, .copy (mbarCopy src dst mb)⟩, ⟨4, .wait mb 0 true⟩, ⟨5, .rd dst (payload.map some)⟩,
    ⟨6, .bar 0⟩, ⟨7, .exit⟩]
    else if g = 1 then [⟨6, .bar 0⟩, ⟨8, .rd dst (payload.map some)⟩, ⟨9, .exit⟩] else []
  barriers c := if c = 0 then [.arrival 0 0 none fwdLanes] else []
  rf _ _ := some (.async (0, 3) (.write .copy))
  async := { copies := fun i => if i = (0, 3) then done payload else {} }
  objects m := if m = mb then fwdLog else []

example : MBarrier.CheckedLog fwdLog :=
  MBarrier.checkedLog_of_replay (ops := [(.thread (0, 0), .init 1),
    (.thread (0, 2), .arrive 1 16), (.async (0, 3) (.notify .copy), .completeTx 16),
    (.thread (0, 4), .pollParity 0 true)]) (by rfl) (by decide)

theorem fwd_copy :
    fwd.Copy (0, 3) (mbarCopy src dst mb) ∧ ∃ bs, (fwd.async.copies (0, 3)).writeBytes = some bs :=
  ⟨⟨3, rfl⟩, payload, rfl⟩
theorem fwd_observed : AsyncObserved fwd (0, 3) (.write .copy) (0, 4) true .cta := by
  refine ⟨.async (0, 3) (.notify .copy), mb,
    .inl ⟨rfl, 16, mbarCopy src dst mb, rfl, rfl, rfl, rfl⟩, ⟨⟨4, 0, rfl⟩, ?_⟩⟩
  change MBarrier.UpdateBeforeWait fwdLog _ _
  exact ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩
theorem waiter_sees_copy : ∃ w, AsyncFinished launch fwd (0, 3) (.write .copy) w ∧
    baseCausality launch fwd w (0, 5) :=
  ⟨(0, 4), .inr ⟨.cta, fwd_observed, by
    simp [ScopesMeet, MbarScopeIncludes, SameCta, SameCluster, Launch.threads, launch]⟩,
    .single (.inl ⟨rfl, by decide, by decide⟩)⟩
theorem barrier_forwards_copy :
    ∃ w, AsyncFinished launch fwd (0, 3) (.write .copy) w ∧ baseCausality launch fwd w (1, 1) := by
  obtain ⟨w, hw, hh⟩ := waiter_sees_copy
  refine ⟨w, hw, hh.trans ?_⟩
  exact bar_baseCausality (i := 6) (j := 0) (k := 0) ⟨by decide, by decide, rfl⟩
    (by exact ⟨by decide,⟨none,6,rfl⟩,0,{},0,none,fwdLanes,0,
      rfl,rfl,by decide,rfl,fwdState,rfl⟩)
    (by exact ⟨by decide,⟨none,6,rfl⟩,0,{},0,none,fwdLanes,1,
      rfl,rfl,by decide,rfl,fwdState,rfl⟩) (by decide) (by decide) (by decide)

-- The copy completed phase 0. Polling parity 1 fails; consuming anyway is unsafe.
def wrongLog := regressionLog [(.thread (0, 0), .init 1), (.thread (0, 2), .arrive 1 16),
  (.async (0, 3) (.notify .copy), .completeTx 16), (.thread (0, 4), .pollParity 1 false)]
def wrongPhase : Execution where
  tr g := if g = 0 then [⟨0, .mbInit mb 1⟩, ⟨1, fenceAsync⟩, ⟨2, .arrive mb 16⟩,
    ⟨3, .copy (mbarCopy src dst mb)⟩, ⟨4, .wait mb 1 false⟩, ⟨5, .rd dst (payload.map some)⟩,
      ⟨6, .exit⟩] else []
  rf _ _ := some (.async (0, 3) (.write .copy))
  async := { copies := fun i => if i = (0, 3) then done payload else {} }
  objects m := if m = mb then wrongLog else []

example : MBarrier.CheckedLog wrongLog :=
  MBarrier.checkedLog_of_replay (ops := [(.thread (0, 0), .init 1),
    (.thread (0, 2), .arrive 1 16), (.async (0, 3) (.notify .copy), .completeTx 16),
    (.thread (0, 4), .pollParity 1 false)]) (by rfl) (by decide)

theorem wrong_not_visible (f : EvId) :
    ¬ ∃ w, AsyncFinished launch wrongPhase (0, 3) (.write .copy) w ∧
      baseCausality launch wrongPhase w f := by
  rintro ⟨w, hfin, -⟩
  rw [asyncFinished_copy_of_mbarrier launch (s := mbarCopy src dst mb) ⟨3, rfl⟩ rfl] at hfin
  obtain ⟨_, ⟨n, m, hn, -, i, j, r, wr, phase, _, _, _, hw, _, _, hwait, _⟩, -⟩ := hfin
  rw [notifies_copy_of_mbarrier (s := mbarCopy src dst mb) ⟨3, rfl⟩ rfl (Or.inr rfl)] at hn
  obtain ⟨-, -, s, hi, -, hm, -⟩ := hn
  have hs : s = mbarCopy src dst mb := by simpa [issuedBy, Execution.get, wrongPhase] using hi.symm
  subst s
  have hm1 : mb = m := by injection hm
  subst hm1
  have hwmem := List.mem_of_getElem? hw
  change wr ∈ [_, _, _, _] at hwmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwmem
  rcases hwmem with rfl | rfl | rfl | rfl <;> cases hwait

private theorem wrong_no_bar (e : EvId) (k : Nat) : ¬ wrongPhase.BarK e k := by
  rintro ⟨⟨id, pc, he⟩, _⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g; have hm := List.mem_of_getElem? he; simp [wrongPhase] at hm
  · simp [Execution.IsBarrier, Execution.get, wrongPhase, hg] at he
private theorem wrong_no_wait (e : EvId) (m : Loc) : ¬ wrongPhase.AcquireWait e m := by
  rintro ⟨pc, p, sc, he⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g; have hm := List.mem_of_getElem? he; simp [wrongPhase] at hm
  · simp [Execution.get, wrongPhase, hg] at he

theorem wrong_phase_unsafe (mem0 : Mem0) : Unsafe launch { name := "k", params := [], code :=
                                                           [] } [] mem0 wrongPhase := by
  apply Or.inr; apply Or.inr; apply Or.inl
  apply copy_unwaited (c := (0, 3)) (e := (0, 5)) ⟨3, rfl⟩ ⟨5, rfl⟩
    (show dst.Covers dst.loc from ⟨rfl, rfl, by decide, by decide⟩)
    (by
      rintro ⟨g, j⟩ d s accum mask ⟨pc, h⟩
      have hm := List.mem_of_getElem? h
      simp only [wrongPhase] at hm
      split_ifs at hm <;> simp at hm)
    (by
      rintro ⟨g, j⟩ c ⟨pc, h⟩
      have hm := List.mem_of_getElem? h
      simp only [wrongPhase] at hm
      split_ifs at hm <;> simp at hm)
    (wrong_not_visible _)
  rintro ⟨f, _, _, ⟨pc, hf⟩, _, _, _, hbefore, -⟩
  have hf2 : f = (0,1) := by
    obtain ⟨g,i⟩ := f
    have hm := List.mem_of_getElem? hf
    simp only [wrongPhase] at hm
    split_ifs at hm with hg
    · subst g
      have hil : i < 7 := (List.getElem?_eq_some_iff.mp hf).1
      interval_cases i <;> simp_all [Execution.get,wrongPhase]
    · simp at hm
  subst f
  have hk : ∀e pc k, wrongPhase.get e = some ⟨pc,k⟩ → legacyKind k = true := by
    intro e pc k hi
    have hm := List.mem_of_getElem? hi
    simp only [wrongPhase] at hm
    split_ifs at hm <;> simp_all only [List.mem_cons,List.not_mem_nil,or_false,Event.mk.injEq]
    all_goals
      repeat' (rcases hm with hm | hm)
    all_goals simp_all [legacyKind]
  have hh := baseCausality_legacy hk (fun _ => rfl) hbefore
  have step : ∀a b, (po wrongPhase a b ∨ CtaBarSync launch wrongPhase a b ∨
    MSync launch wrongPhase a b) → a.2 < b.2 := by
    intro a b hh
    rcases hh with hp | hs | hm
    · exact hp.2.1
    · obtain ⟨_,key,i,j,hi,_⟩ := hs
      obtain ⟨idx,st,warp,count,lanes,g,hget,_⟩ := hi.2.2
      simp [wrongPhase] at hget
    · obtain ⟨x,w,m,rs,ws,-,⟨⟨pc,parity,hw⟩,_⟩,_⟩ := hm
      exact (wrong_no_wait w m ⟨pc,parity,ws,hw⟩).elim
  have ordered : ∀{a b}, Relation.TransGen
      (fun a b => po wrongPhase a b ∨ CtaBarSync launch wrongPhase a b ∨
        MSync launch wrongPhase a b) a b → a.2 < b.2 := by
    intro a b hp
    induction hp with
    | single hedge => exact step _ _ hedge
    | tail _ hedge ih => exact ih.trans (step _ _ hedge)
  have hlt : 5 < 1 := ordered hh
  omega
end TmaScope

/-! ### A local loop violates `progress` -/

/-- `L0: bra L0`. -/
def spin : Kernel := { name := "spin", params := [], code := [{ op := .bra 0 false }] }

theorem spin_tau {L : Launch} {g : Nat} {t : TState} (hpc : t.pc = 0) (hf : t.fault = none) :
    out spin [] L g t = .tau { t with pc := 0 } := by
  obtain ⟨pc, regs, sub, acc, fault⟩ := t
  simp only at hpc hf
  subst hpc hf
  rfl

theorem spin_no_event {L : Launch} {g : Nat} {t : TState} {e : Event} {o : Option TState}
    {l : List Event} (h : Run spin [] L g t (e :: l) o) (hpc : t.pc = 0) (hf : t.fault = none) :
    False := by
  have key : ∀ t1, Relation.ReflTransGen (Tau spin [] L g) t t1 → t1.pc = 0 ∧ t1.fault = none := by
    intro t1 h1
    induction h1 with
    | refl => exact ⟨hpc, hf⟩
    | tail _ hs ih =>
      unfold Tau at hs
      rw [spin_tau ih.1 ih.2] at hs
      cases hs
      exact ⟨rfl, ih.2⟩
  have stuck : ∀ t1 e o, Relation.ReflTransGen (Tau spin [] L g) t t1 →
      ¬ EStep spin [] L g t1 e o := by
    rintro t1 e o h1 ⟨m, hm, -⟩
    obtain ⟨h1, h2⟩ := key t1 h1
    rw [spin_tau h1 h2] at hm
    cases hm
  cases h with
  | step hl he _ => exact stuck _ _ _ hl he
  | last hl he => exact stuck _ _ _ hl he

theorem empty_consistent (L : Launch) (hl : L.clusterGridValid) (mem0 : Mem0) :
    Consistent L spin [] mem0 .empty :=
  consistent_empty hl (by simp)

/-- `spin` has a maximal execution in which no thread ended, so it is not `Correct` for any
launch with a thread, whatever the postcondition. -/
theorem spin_not_progress (L : Launch) (hv : L.Valid spin) (hL : 0 < L.threads) (mem0 : Mem0)
    (post : FinalMem → Prop) : ¬ Correct spin [] L mem0 post := by
  intro hc
  have hmax : Maximal L spin [] mem0 .empty := by
    refine ⟨empty_consistent L hv.1 mem0, fun Y hY _ => ?_⟩
    have hnil : ∀ g, Y.tr g = [] := by
      intro g
      by_cases hg : g < L.threads
      · obtain ⟨o, hr⟩ := hY.thr g hg
        cases hl : Y.tr g with
        | nil => rfl
        | cons e l => rw [hl] at hr; exact (spin_no_event hr rfl rfl).elim
      · exact hY.outside g (by omega)
    have hn : Y.NoTma := by
      intro e pc kind he
      simp [Execution.get, hnil] at he
    rw [hn.size_eq hY]
    simp [hnil, Execution.size, Execution.threadSize, Execution.pairSize, Execution.empty]

  have hn : Execution.empty.NoTma := by
    intro e pc kind he
    simp [Execution.get, Execution.empty] at he
  obtain ⟨pc, h⟩ := (hn.complete_iff L (empty_consistent L hv.1 mem0).clc).mp
    (hc.progress hv _ hmax) 0 hL
  simp [Execution.empty] at h

end

end PTX
