-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Scalar
public import Kernels.InklingRelDecode.Proof.Lib.PollEvent

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow MbarRow

def Object.pc : Object → Nat | .score _ => 1257 | .prob _ => 2510 | .done => 2239
def Object.index : Object → Nat | .score s | .prob s => s.val | .done => 0
def Object.width : Object → Nat | .score _ | .prob _ => 2 | .done => 1
def Object.visits (o : Object) (n : Nat) := (n+o.width-1-o.index)/o.width

def Object.atRound : Object → Nat → Object
  | .score _, n => .score (slot2 n) | .prob _, n => .prob (slot2 n) | .done, _ => .done

private theorem visit_step (o : Object) (n : Nat) :
    o.visits (n+1) = o.visits n + if o=o.atRound n then 1 else 0 := by
  cases o <;> simp only [Object.visits,Object.atRound,Object.width,Object.index]
  all_goals simp
  all_goals split <;> rename_i eq
  all_goals first | (apply_fun Fin.val at eq; change _=n%2 at eq; omega) |
    (have ne : _≠n%2 := fun h => eq (Fin.ext h); omega)

theorem wait_obj {Q L X g k c o pc q ok a sc} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨pc,.wait (Object.loc o L c) q ok a sc⟩) :
    g/L.block=c ∧ pc=o.pc ∧ o=o.atRound (roundAt X g k pc) ∧
      q=roundAt X g k pc/o.width%2 := by
  obtain ⟨cta,use⟩ := uses rows hg he rfl
  refine ⟨cta,?_⟩
  generalize h : (Event.mk pc (.wait (Object.loc o L c) q ok a sc))=e at use
  cases use with
  | init kind => cases h; cases kind
  | scoreCommit _ _ kind | doneCommit _ _ kind => cases h; obtain ⟨_,kd,_⟩ := kind; cases kd
  | probArrive _ _ kind => cases h; cases kind
  | scoreWait pos _ kind | probWait pos _ kind | doneWait pos _ kind =>
    cases h
    obtain ⟨_,hk⟩ := kind
    cases pos
    obtain ⟨_,rfl,_⟩ := Kind.wait.inj hk
    exact ⟨rfl,rfl,by simp [Object.width]⟩

theorem wait_pc {Q L X g k l q ok a sc} (rows : MbarRows Q L X) (hg : g<L.threads)
    (o : Object) (he : X.get (g,k)=some ⟨o.pc,.wait l q ok a sc⟩) :
    l=(o.atRound (roundAt X g k o.pc)).loc L (g/L.block) := by
  cases mbar_use rows hg he (l := l) rfl with
  | startup _ h | dispatch _ h => cases h
  | prologue _ h =>
    cases h with
    | init _ _ _ h _ _ _ _ _ | preloadArrive _ _ _ h => cases h
    | preloadCopy _ _ _ h => obtain ⟨_,_,h,_⟩ := h; cases h
  | epilogue _ h =>
    cases h with | finalWait pos _ _ => cases o <;> cases pos
  | loader _ h =>
    cases h with
    | emptyWait pos _ _ => cases o <;> cases pos
    | readyArrive _ _ _ h => cases h
    | readyCopy _ _ _ h => obtain ⟨_,_,h,_⟩ := h; cases h
  | softmax _ h =>
    cases h with
    | sWait pos addr _ | oWait pos addr _ => cases o <;> first | exact addr | cases pos
    | pArrive _ _ _ h => cases h
  | mma _ h =>
    cases h with
    | readyWait pos _ _ => cases o <;> cases pos
    | pWait pos addr _ => cases o <;> first | exact addr | cases pos
    | sCommit _ _ h | doneCommit _ _ h | emptyCommit _ _ h | finalCommit _ _ h =>
      obtain ⟨_,kd,_⟩ := h; cases kd

theorem count {Q L X g} (rows : MbarRows Q L X) (hg : g<L.threads) (o : Object) (k : Nat) :
    okPolls (o.loc L (g/L.block)) ((X.tr g).take k)=o.visits (roundAt X g k o.pc) := by
  apply Lib.PollEvent.count_index (fun n => decide (o=o.atRound n)) o.visits
  · cases o <;> simp [Object.visits,Object.width,Object.index]
  · intro n; simpa using visit_step o n
  · intro j e get
    constructor
    · intro hit
      obtain ⟨p,q,ac,sc,rfl⟩ := Lib.PollEvent.obj_iff.mp hit
      obtain ⟨_,rfl,slot,_⟩ := wait_obj rows hg get
      exact ⟨Lib.PollEvent.at_iff.mpr ⟨_,_,_,_,rfl⟩,decide_eq_true slot⟩
    · rintro ⟨hit,slot⟩
      obtain ⟨l,q,ac,sc,rfl⟩ := Lib.PollEvent.at_iff.mp hit
      have addr := wait_pc rows hg o get
      change decide (o=o.atRound (roundAt X g j o.pc))=true at slot
      rw [←of_decide_eq_true slot] at addr
      exact Lib.PollEvent.obj_iff.mpr ⟨_,_,_,_,by rw [addr]⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
