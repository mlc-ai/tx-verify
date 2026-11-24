-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActiveEntryProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderActiveProgram
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

private theorem wordReadOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X)
    {g i pc base off ra rd value : Nat} (hg : g < l.threads)
    {s t : TState} {F : List (Nat × Value)}
    (hLo : 174 ≤ pc) (hHi : pc < 1906)
    (hCode : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
        addr := ⟨.reg ra 64, Int.ofNat off⟩, dsts := [some rd] }⟩)
    (ht : At t pc F) (hPtr : t.regs ra = some (b64 base))
    (hFit : base + off < 2 ^ 64) (hAlign : (base + off) % 4 = 0)
    (hValue : HasValue m (globalLoc (base + off)) (b32 value))
    (hFree : ∀ k < 4, ∀ w a data, X.MemWrites w a data →
      ¬ a.Covers ((globalLoc (base + off)).at k))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ rd)
    {ending : Option TState}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some s))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop i) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hPos : 0 < i) (hBound : i ≤ (X.tr g).length)
    (hRelease : i = (X.tr g).length → Step.Released l X g) :
    ∃ u, X.get (g,i) = some ⟨pc,.rd {loc := globalLoc (base+off),size := 4}
        ((b32 value).toBytes.map some)⟩ ∧
      At u (pc+1) ((rd,b32 value) :: F) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (i+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i+1)) ending := by
  have hN := loaderWordReadNext (l := l) (g := g) hLo hHi hCode ht hPtr hFit hAlign
  have hNext : Next kernel Assumptions.all l g s t
      (.read {loc := globalLoc (base+off),size := 4} (afterLoad t [rd])) := ⟨hLocal,hN.stop⟩
  obtain ⟨he,hPast,hTail⟩ := Step.protected_read_of_maximal hMax hg (value := b32 value)
    (a := {loc := globalLoc (base+off),size := 4})
    rfl hValue hFree hNext hPrefix hr hPos hBound hRelease
    (Assumptions.wf_snoc_initial hMax.1)
  have hRebuild := PTX.Proof.rebuild_scalar (v := b32 value) (show 0 < 4 by decide) rfl
  have hAfter : afterLoad t [rd] ((b32 value).toBytes.map some) =
      next (setReg t rd (b32 value)) := by
    rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild]
    simp [next,setReg,ht.2.1,ht.2.2.1]
  rw [hAfter] at hPast hTail
  exact ⟨_,ht.1 ▸ he,ht.set hFresh,hPast,hTail⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hMax writes

/-- The maximal loader prefix records all three protected metadata reads. -/
theorem activeReadsLaneOfMaximal {g i batch tid tile head : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) {s₀ t : TState} {G : List (Nat × Value)} (hG : ActiveReadExtra G)
    (ht : At t 381 ((loaderActiveFacts p l tid batch ++
      [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ++ G))
    {ending : Option TState}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some s₀))
    (hr : Run kernel Assumptions.all l g s₀ ((X.tr g).drop i) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s₀ t) (hPos : 0 < i)
    (hBound : i ≤ (X.tr g).length) (hRelease : i = (X.tr g).length → Step.Released l X g) :
    ∃ u,
      X.get (g, i) = some ⟨381, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, i + 1) = some ⟨382, .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
        ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      X.get (g, i + 1 + 1) = some ⟨385, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      At u 386 ([(1086, b32 (p.kLength batch)), (1799, b32 (p.qOffset batch)),
        (1800, b32 (p.qOffset (batch + 1))), (1085, b32 ((2 ^ 32 - p.qLength batch) % 2 ^ 32))] ++
        ((loaderActiveFacts p l tid batch ++
          [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ++ G)) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (i+1+1+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1 + 1 + 1)) ending := by
  let F := loaderActiveFacts p l tid batch ++
    [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]
  let base := p.cuQBase + 4 * batch
  let used := p.usedKBase + 4 * batch
  let F₁ := (1799, b32 (p.qOffset batch)) :: (F ++ G)
  let F₂ := (1800, b32 (p.qOffset (batch + 1))) :: (1799, b32 (p.qOffset batch)) :: F
  have hQRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hQRange
  have hKRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hKRange
  have hQAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  have hKAlign := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hQ := hp.cuQ_protected writes
  have noReg {A : List (Nat × Value)} {r : Nat} (h : r ∉ A.map Prod.fst) :
      ∀ x ∈ A, x.1 ≠ r := by
    intro x hm he
    exact h (he ▸ List.mem_map_of_mem hm)
  have hPtr : t.regs 7515 = some (b64 base) := ht.2.2.2.2.1
  obtain ⟨v,he,hV,hPast,hRun⟩ := wordReadOfMaximal hMax hg (off := 0)
    (by decide) (by decide) Flow.code_381
    ht hPtr (by dsimp [base]; omega) (by dsimp [base]; omega)
    (hp.cuQ batch hb.le) (hQ batch hb.le)
    (by
      intro x hx
      exact (List.mem_append.mp hx).elim
        (noReg (show 1799 ∉ F.map Prod.fst from of_decide_eq_true rfl) x) (hG.qlo x))
    hPrefix hr hLocal hPos hBound hRelease
  have hPtr' : v.regs 7515 = some (b64 base) := hV.2.2.2.2.2.1
  have hb' : batch + 1 ≤ p.batch := by omega
  have hEq : base + 4 = p.cuQBase + 4 * (batch + 1) := by dsimp [base]; omega
  obtain ⟨s,he',hS,hPast',hRun'⟩ := wordReadOfMaximal hMax hg (off := 4)
    (by decide) (by decide) Flow.code_382
    hV hPtr' (by rw [hEq]; omega) (by dsimp [base]; omega)
    (by rw [hEq]; exact hp.cuQ (batch + 1) hb')
    (by rw [hEq]; exact hQ (batch + 1) hb')
    (by
      intro x hx
      change x ∈ (1799, b32 (p.qOffset batch)) :: F ++ G at hx
      have hc : x ∈ ((1799, b32 (p.qOffset batch)) :: F) ++ G := hx
      exact (List.mem_append.mp hc).elim
        (noReg (show 1800 ∉ (((1799, b32 (p.qOffset batch)) :: F).map Prod.fst) from
          of_decide_eq_true rfl) x) (hG.qhi x))
    hPast hRun .refl (Nat.succ_pos _) (len_of_get he)
    (releasedIfLast he (by intro h; cases h))
  have hArgs : At s 383 [(1799, b32 (p.qOffset batch)), (1800, b32 (p.qOffset (batch + 1))),
      (7503, b64 p.usedKBase), (7514, b64 (4 * batch))] := by
    apply hS.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup hS.2.2.2.2; rfl)
  obtain ⟨w, hw, hW⟩ := activeUsedKAddress (g := g) hp hb s hArgs
  have hBaseKeep : ((kernel.code.drop 383).take 2).all
      (fun ins => (F₂.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨hwA, hwFrame⟩ := loaderLinear (regs := (F₂ ++ G).map Prod.fst)
    (by decide) (by decide) hS.1
    (by
      apply List.all_eq_true.mpr
      intro ins hi
      rw [List.map_append, List.all_append, List.all_eq_true.mp hBaseKeep ins hi,
        List.all_eq_true.mp hG.prep ins hi]
      rfl) rfl hw
  have hF₂ : Holds w.regs (F₂ ++ G) := holdsSchedulerFrame hS.2.2.2.2 hwFrame
    (fun _ hm => List.mem_map_of_mem hm)
  let F₃ := (7516, b64 used) :: (1085, b32 ((2 ^ 32 - p.qLength batch) % 2 ^ 32)) :: F₂
  have hAt : At w 385 (F₃ ++ G) := hW.mono ⟨hW.2.2.2.2.1, hW.2.2.2.2.2.1, hF₂⟩
  have hUsed : ∀ k < 4, ∀ w a data, X.MemWrites w a data →
      ¬ a.Covers ((globalLoc used).at k) := by
    intro k hk w a data hWrite
    apply hp.inputByte_unwritten writes (region := ⟨p.usedKBase, 4 * p.batch⟩)
    · simp [Params.inputRegions]
    · exact ⟨rfl, rfl, by dsimp [used, globalLoc, Loc.at]; omega,
        by dsimp [used, globalLoc, Loc.at]; omega⟩
    · exact hWrite
  obtain ⟨u,he'',hU,hPast'',hRun''⟩ := wordReadOfMaximal hMax hg (off := 0)
    (by decide) (by decide) Flow.code_385
    hAt hAt.2.2.2.2.1 (by dsimp [used]; omega) (by dsimp [used]; omega)
    (hp.usedK batch hb) hUsed
    (by
      intro x hx
      exact (List.mem_append.mp hx).elim
        (noReg (show 1086 ∉ F₃.map Prod.fst from of_decide_eq_true rfl) x) (hG.used x))
    hPast' hRun' (run_rtg hwA) (Nat.succ_pos _) (len_of_get he')
    (releasedIfLast he' (by intro h; cases h))
  exact ⟨u, he, by simpa only [hEq] using he', he'',
    hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.1,
      hU.2.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.2⟩,hPast'',hRun''⟩

omit hp hMax writes in
/-- The replay frame after the two active CuQ reads and the used-K length read. -/
def loaderInitialMetadataFrame (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  [(1086,b32 (p.kLength batch)),(1799,b32 (p.qOffset batch)),
    (1800,b32 (p.qOffset (batch+1))),(1085,b32 ((2^32-p.qLength batch)%2^32))] ++
    loaderActiveLaneFacts p l g batch lane

/-- All lanes in an active loader warp record the three actual metadata reads,
including a protected used-K read at the selected request's address. -/
theorem recordActiveMetadataWithFrame {g batch shuffles votes : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) {ends : Nat → Option TState} {G : Nat → List (Nat × Value)}
    (cur : SchedulerWarpReached l X g 381 (fun lane => loaderActiveLaneFacts p l g batch lane ++
      G lane) shuffles votes ends) (hExtra : ∀ lane < 32, ActiveReadExtra (G lane)) :
    Nonempty (SchedulerWarpReached l X g 386
      (fun lane => loaderInitialMetadataFrame p l g batch lane ++ G lane) shuffles votes ends) := by
  let thread := warpLane l g
  let events := activeMetadataEvents p batch
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      At u 386 (loaderInitialMetadataFrame p l g batch lane ++ G lane) ∧
      ((X.tr (thread lane)).drop (cur.pos lane) =
        events ++ (X.tr (thread lane)).drop (cur.pos lane+3)) ∧
      X.get (thread lane,cur.pos lane+2) = some
        ⟨385,.rd {loc := globalLoc (p.usedKBase+4*batch),size := 4}
          ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (cur.pos lane+3)) (some u) ∧
      Run kernel Assumptions.all l (thread lane) u
        ((X.tr (thread lane)).drop (cur.pos lane+3)) (ends lane) := by
    let coords := assignedCoordinates p batch (g/l.block)
    let tid := thread lane % l.block
    have ht : At (cur.state lane) 381 ((loaderActiveFacts p l tid batch ++
        [(7168,b32 coords.1),(7169,b32 coords.2),(7170,b32 batch),(7296,b64 16)]) ++ G lane) := by
      simpa only [loaderActiveLaneFacts,tid,thread,coords] using
        cur.checkpoint lane hl
    have hThread : thread lane < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    obtain ⟨u,hLo,hHi,hUsed,hAt,hPast,hTail⟩ := activeReadsLaneOfMaximal hp hMax writes
      hThread hb (hExtra lane hl) ht (cur.recorded lane hl) (cur.continuation lane hl)
      (cur.localSteps lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
    have hAdd : cur.pos lane+1+1+1 = cur.pos lane+3 := by omega
    refine ⟨u,?_,?_,hUsed,hAdd ▸ hPast,hAdd ▸ hTail⟩
    · simpa only [loaderInitialMetadataFrame,loaderActiveLaneFacts,tid,thread,coords,
        List.append_assoc]
        using hAt
    · have hL := List.getElem?_eq_some_iff.mp hLo
      have hH := List.getElem?_eq_some_iff.mp hHi
      have hU := List.getElem?_eq_some_iff.mp hUsed
      rw [List.drop_eq_getElem_cons hL.1,hL.2,List.drop_eq_getElem_cons hH.1,hH.2,
        List.drop_eq_getElem_cons hU.1,hU.2,hAdd]
      rfl
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hAt hEvents hGet hRun hTail using hLane
  have hCount := cur.ordinals.advance (fun _ => events)
    (fun lane hl => ⟨_,hEvents lane hl⟩) (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨fun lane => cur.pos lane+3,u,u,hCount,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    ?_,?_,hRun⟩⟩
  · exact fun lane hl => len_of_get (hGet lane hl)
  · exact fun lane hl => releasedIfLast (hGet lane hl) (by intro h; cases h)

end PTX.Kernels.TmlFa4Fwd.Loader
