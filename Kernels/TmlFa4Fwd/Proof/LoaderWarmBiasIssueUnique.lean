-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasCoverage
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasCursor
import Lemmas.Order.WaitOrderEnables
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue Thread.Loader

/-- Two actual issues of a warm half at the same shuffle rank are the same issue. -/
theorem warmBiasIssueUniqueAtRank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (stage half : Fin 2) {g first last : Nat}
    (hw : warpIndex l g = 14) (hCTA : g/l.block < tilePrefix p p.batch*p.heads)
    {a b : Nat} {spec other : TensorCopy.Spec}
    (hFirst : X.get (g,first) = some ⟨warmBiasIssueSite stage half,.tensorIssue a spec⟩)
    (hLast : X.get (g,last) = some ⟨warmBiasIssueSite stage half,.tensorIssue b other⟩)
    (hRank : ((X.tr g).take first).countP Execution.isShfl =
      ((X.tr g).take last).countP Execution.isShfl) : first = last := by
  have exclude {i j a b : Nat} {spec other : TensorCopy.Spec}
      (hFirst : X.get (g,i) = some ⟨warmBiasIssueSite stage half,.tensorIssue a spec⟩)
      (hLast : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue b other⟩)
      (hRank : ((X.tr g).take i).countP Execution.isShfl =
        ((X.tr g).take j).countP Execution.isShfl)
      (hLt : i < j) : False := by
    obtain ⟨_,_,_,_,_,_,pos,hPos,s,_,hs,hRun,hEarlier⟩ :=
      warmBiasEntryOfIssue hp hX stage half hw
        (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hFirst
    let events := (X.tr g).drop pos
    have hSplit (q : Nat) (h : pos ≤ q) :
        ((X.tr g).take q).countP Execution.isShfl =
          ((X.tr g).take pos).countP Execution.isShfl +
            (events.take (q-pos)).countP Execution.isShfl := by
      conv_lhs => rw [← Nat.add_sub_of_le h]
      rw [List.take_add,List.countP_append]
    have he : (events.take (j-pos)).countP Execution.isShfl < 64 := by
      rw [hSplit i hPos,hSplit j (hPos.trans hLt.le)] at hRank
      change (events.take (i-pos)).countP Execution.isShfl < 64 at hEarlier
      omega
    obtain ⟨visited,hWalk⟩ := Mma.walkFromRun hRun
    have hBound := warmIssueCountOfRankedPrefix stage half hWalk hs.1 (ringShapeOfAt hs)
      (j-pos) he
    let mark := fun (ev : Event) => ev.pc == warmBiasIssueSite stage half
    have hA : events[i-pos]? = some ⟨warmBiasIssueSite stage half,.tensorIssue a spec⟩ := by
      dsimp [events]
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
      exact hFirst
    have hB : events[j-pos]? = some ⟨warmBiasIssueSite stage half,.tensorIssue b other⟩ := by
      dsimp [events]
      rw [List.getElem?_drop,Nat.add_sub_of_le (hPos.trans hLt.le)]
      exact hLast
    have grow {n : Nat} {e : Event} (hEvent : events[n]? = some e) (hMark : mark e = true) :
        (events.take (n+1)).countP mark = (events.take n).countP mark+1 := by
      obtain ⟨hn,heq⟩ := List.getElem?_eq_some_iff.mp hEvent
      rw [List.take_add,List.drop_eq_getElem_cons hn,heq]
      simp [hMark]
    have hYesA : mark ⟨warmBiasIssueSite stage half,.tensorIssue a spec⟩ = true := by simp [mark]
    have hYesB : mark ⟨warmBiasIssueSite stage half,.tensorIssue b other⟩ = true := by simp [mark]
    have hMarkA := grow hA hYesA
    have hMarkB := grow hB hYesB
    have hMono := countP_take_mono mark events (show i-pos+1 ≤ j-pos by omega)
    change (events.take (j-pos+1)).countP mark ≤ 1 at hBound
    omega
  rcases Nat.lt_trichotomy first last with h | h | h
  · exact (exclude hFirst hLast hRank h).elim
  · exact h
  · exact (exclude hLast hFirst hRank.symm h).elim

end PTX.Kernels.TmlFa4Fwd.Loader
