-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaInitialPolls
import Kernels.TmlFa4Fwd.Proof.MmaPoll
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseUse
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
import Kernels.TmlFa4Fwd.Flow.Code.Part033

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.MBarrier

/-- Starting at the actual selected metadata cursor, record the first Q0 acquire once the
query-ready object reaches phase one. The result keeps the exact replay cursor and trip count. -/
theorem selectedFirstQueryWaitOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pos batch tile : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (htile : 256 * tile < p.qLength batch) {s t : TState} {ending : Option TState}
    (ht : At t 2109 [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
      (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (hCuQ : ∀ lane ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + lane))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hReady : let log := X.objects ⟨.shared,g/l.block,l.sharedBase⟩
      ∃ initial, stateBefore log log.length = some initial ∧ initial.phase = 1)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ n after v,
      X.get (g,pos+3+n) = some ⟨2141,.wait ⟨.shared,g/l.block,l.sharedBase⟩ 0 true true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+3+n+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos+3+n+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after v ∧
      At v 2144 [(2535,b32 l.sharedBase),(2536,b32 0),(1189,b32 (trips p batch tile))] := by
  obtain ⟨r, hPtr, hR⟩ := selectedTripPointer hp g hb t ht
  obtain ⟨v,hV,hPast,hTail,hLen,hReleased⟩ := tripReadsOfMaximal hp hMax hg hb
    (by omega) hR hCuQ hUsedK hPrefix hRun (hLocal.trans (run_rtg hPtr)) hPos hBound hRelease
  obtain ⟨u,hToQuery,hU⟩ := runToFirstQPoll hp g hb htile v hV
  let F := [(2535,b32 l.sharedBase),(2536,b32 0),(1189,b32 (trips p batch tile))]
  have hBase : l.sharedBase < 2^32 := by have := hp.shared.2.1; omega
  have hAligned : l.sharedBase % 8 = 0 := by have := hp.shared.1; omega
  have hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite 0).result := by
    intro pair hm
    simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact of_decide_eq_true rfl
  exact waitOfMaximal hMax hg 0 (phase := 0) hBase hAligned (by decide)
    (F := F) hFresh (by simp [F,waitSite]) (by simp [F,waitSite])
    (fun _ _ _ => by
      obtain ⟨initial,hState,hPhase⟩ := hReady
      exact ⟨initial,hState,by rw [hPhase]; decide⟩)
    (by omega) hLen hReleased hU hPast hTail (run_rtg hToQuery)

/-- A successful opening query wait followed by ready phase one makes the
opening K acquire appear in this maximal MMA lane's trace. -/
theorem firstKeyWaitAfterQueryOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pos : Nat} (hg : g < l.threads) (hw : Prologue.warpIndex l g = 12)
    {s t : TState} {ending : Option TState}
    (ht : At t 2144 [(2535,b32 l.sharedBase),(2536,b32 0)])
    (hReady : let log := X.objects (Thread.Mma.Observation.readyObject l g 0)
      ∃ initial, stateBefore log log.length = some initial ∧ initial.phase = 1)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ i, Thread.Mma.ReadyPoll l X g i 0 0 true .cta ∧
      (Thread.Mma.atPrefix l X g i).kvAcquires 0 = 0 := by
  have hBase : l.sharedBase+32 < 2^32 := by have := hp.shared.2.1; omega
  let F := [(2537,b32 (l.sharedBase+32)),(2536,b32 0)]
  have hSeg : Seg kernel [] l g 1 2144 [(2535,b32 l.sharedBase),(2536,b32 0)] 2145 F := by
    intro v hv
    dsimp only [F]
    seg_fp hv using norm_bits
  obtain ⟨u,hLocal',hu⟩ := hSeg t ht
  have hTau := localRun (by decide) (by decide) ht.1 rfl hLocal'
  have hAligned : (l.sharedBase+32)%8 = 0 := by have := hp.shared.1; omega
  have hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite 1).result := by
    intro pair hm
    simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> exact of_decide_eq_true rfl
  obtain ⟨n,_,_,he,_,_,_,_⟩ := waitOfMaximal hMax hg 1 (phase := 0) hBase hAligned (by decide)
    (F := F) hFresh (by simp [F,waitSite]) (by simp [F,waitSite])
    (fun _ _ _ => by
      obtain ⟨initial,hState,hPhase⟩ := hReady
      exact ⟨initial,hState,by rw [hPhase]; decide⟩)
    hPos hBound hRelease hu hPrefix hRun (hLocal.trans (run_rtg hTau))
  exact ⟨pos+n,⟨_,he,rfl⟩,Thread.Mma.firstKeyAcquireOrdinal hp hMax.1 hw he⟩

end PTX.Kernels.TmlFa4Fwd.Mma
