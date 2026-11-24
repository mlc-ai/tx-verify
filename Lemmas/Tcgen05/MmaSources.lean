-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ByteCausalityAcyclic
public import Lemmas.Order.CommitOperandFrame

public import Core.Tc.TcMmaCompletion
public import Lemmas.Tcgen05.MmaComplete
public import Lemmas.Tcgen05.MmaFinishConsistent
public import Lemmas.Async.AsyncOrder
public import Lemmas.Order.GuardObserver

@[expose] public section

section
namespace PTX.TcMma
noncomputable section

/-- Notification, object/resource records and snapshot changes preserve this
law whenever source issue events and completion bits are unchanged. -/
theorem completionClosed_frame {L : Launch} {X Y : Execution}
    (hissues : ∀i d s a m,X.MmaIssue i d s a m ↔Y.MmaIssue i d s a m)
    (hdone : ∀i,X.async.mmaDone i=Y.async.mmaDone i)
    (hX : CompletionClosed L X) : CompletionClosed L Y := by
  intro i j hp hj
  rw [←hdone i]
  apply hX i j ((completionPrecedes_congr hissues).mpr hp)
  rwa [hdone j]

end
end PTX.TcMma
end

section
namespace PTX
open AsyncCopy
noncomputable section
variable {X : Execution} {i : EvId} {values : MmaOperands} {ra rb : Nat → Option Ref}

/-- The source chosen for a new operand read. -/
def mmaReadSource (ra rb : Nat → Option Ref) (isB : Bool) (k : Nat) : Option Ref :=
  if isB then rb k else ra k

/-- The value a completed MMA records for an operand byte. -/
def mmaReadValue (values : MmaOperands) (isB : Bool) (k : Nat) : Option (Option Byte) :=
  (if isB then values.b else values.a)[k]?

theorem finishMma_reads
    {e : Ref} {a : Acc} {bs : List (Option Byte)}
    (hr : (X.finishMma i values ra rb).MemReads e a bs) :
    X.MemReads e a bs ∨
      ∃ isB k b, e = .async i (.mmaRead isB k) ∧ X.MmaFootprint i isB k a.loc ∧ a.size = 1 ∧
        mmaReadValue values isB k = some b ∧ bs = [b] := by
  cases e with
  | thread j => exact .inl hr
  | async j p =>
    cases p <;> simp only [Execution.MemReads] at hr
    all_goals try exact Or.inl hr
    rename_i isB index
    obtain ⟨byte, ⟨hf, operands, hop, hv⟩, hn, hbs⟩ := hr
    by_cases he : j = i
    · subst j
      have hvalues : operands = values := by simpa [Execution.finishMma] using hop.symm
      subst hvalues
      exact .inr ⟨isB, index, byte, rfl, hf, hn, hv, hbs⟩
    · exact .inl ⟨byte, ⟨hf, operands,
        by simpa [Execution.finishMma, he] using hop, hv⟩, hn, hbs⟩

/-- With no recorded operands, the new reads cannot overwrite any existing read. -/
theorem le_finishMma_unstarted (hn : X.async.mmaOperands i = none) :
    X.le (X.finishMma i values ra rb) := by
  apply Execution.le_finishMma
  · intro old hv; rw [hn] at hv; cases hv
  · rintro k a bs ⟨b, ⟨_, operands, hop, _⟩, _⟩
    rw [hn] at hop; cases hop
  · rintro k a bs ⟨b, ⟨_, operands, hop, _⟩, _⟩
    rw [hn] at hop; cases hop

/-- New one-byte operand reads have concrete sources covering their descriptor address.
All existing reads keep their old sources and values. -/
theorem finishMma_rf {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X)
    (hle : X.le (X.finishMma i values ra rb))
    (hab : ∀ isB k loc b, X.MmaFootprint i isB k loc → mmaReadValue values isB k = some b →
      ∃ w a bs, mmaReadSource ra rb isB k = some w ∧ X.MemWrites w a bs ∧
        a.Covers loc ∧ b = wbyte a bs loc) :
    RfWf mem0
      (X.finishMma i values ra rb) := by
  intro e a bs hr
  rcases finishMma_reads hr with hold | ⟨isB, k, b, rfl, hf, hsize, hv, rfl⟩
  · obtain ⟨hlen, hrf⟩ := hX.rf e a bs hold
    refine ⟨hlen, fun j hj => ?_⟩
    rw [hle.2.1 e j ⟨a, bs, hold⟩]
    have h := hrf j hj
    cases hs : X.rf e j with
    | none => rw [hs] at h; exact h
    | some w =>
      rw [hs] at h
      obtain ⟨a', bs', hw, hc, hv⟩ := h
      exact ⟨a', bs', finishMma_memWrites.mpr hw, hc, hv⟩
  · refine ⟨by simp [hsize], ?_⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    obtain ⟨w, target, bytes, hs, hw, hc, hb⟩ := hab isB k a.loc b hf hv
    have hsrc : (X.finishMma i values ra rb).rf (.async i (.mmaRead isB k)) 0 = some w := by
      simp only [Execution.finishMma, and_self, ↓reduceIte]
      cases isB <;> simpa [mmaReadSource] using hs
    rw [hsrc]
    exact ⟨target, bytes, finishMma_memWrites.mpr hw, by simpa [Loc.at] using hc,
      by simpa [Loc.at] using congrArg some hb⟩

/-- Before arithmetic completion, no operand-read completion has been observed. -/
theorem uncompleted_mma_no_visibility {L : Launch} (hm : CommitOk X)
    (hn : X.async.mmaDone i = false) {p : Part} (hp : MmaPart p) {l : Loc} {f : Ref} :
    ¬ modelCausality L X l (.async i p) f := by
  have noObservation : ∀ w ws, ¬ AsyncObserved X i .mmaDone w true ws := by
    rintro w ws ⟨n, m, ⟨c, spec, rank, rfl, htrack, _, _, hnotify⟩, _⟩
    have hd := (hm c rank hnotify).2 i htrack
    rw [hn] at hd
    cases hd
  -- no group wait makes an MMA stage visible
  have notGroup : ∀ k, GroupWaitVisible k p = false := by
    intro k
    cases p <;> simp only [MmaPart] at hp <;> rcases k with (_ | _) | _ <;> rfl
  have notFinished : ∀ w, ¬ AsyncFinished L X i p w := by
    intro w
    rintro (⟨k, hk, -⟩ | ⟨ws, h, -⟩)
    · rw [notGroup] at hk
      cases hk
    · cases p <;> first
        | exact False.elim hp
        | exact noObservation w ws h
  have notOnly : ∀ w, ¬ AsyncOnlyFinished X i p w := by
    rintro w ⟨hk, -⟩
    rw [notGroup] at hk
    cases hk
  cases f with
  | thread j => exact fun ⟨_, w, ho, _⟩ => notFinished w ho
  | async j q =>
    intro h
    obtain ⟨_,edge⟩ := AsyncChain.first h.2
    rcases edge.2.2 with ⟨w,ho,_⟩ | ⟨w,ho,_⟩
    · exact notFinished w ho
    · exact notOnly w ho

theorem finishMma_noFuture {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X)
    (hle : X.le (X.finishMma i values ra rb))
    (hn : X.async.mmaDone i = false) :
    NoFuture L (X.finishMma i values ra rb) := by
  intro e a bs k w hr hk hs hv
  have hv' := ByteCausality.reflect_of_same_tr hle rfl hX.tma.2.1 hX.tcCommit
    (fun h => (finishMma_modelCausality hX.tcCommit hn).mp h) (fun h => h) hv
  rcases finishMma_reads hr with hold | ⟨isB, q, b, rfl, _, _, _, rfl⟩
  · exact hX.noFuture e a bs k w hold hk ((hle.2.1 e k ⟨a, bs, hold⟩).symm.trans hs) hv'
  · obtain ⟨dst, edge⟩ := hv'.starts
    exact uncompleted_mma_no_visibility hX.tcCommit hn (p := .mmaRead isB q) True.intro edge

theorem finishMma_hidden {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X)
    (hle : X.le (X.finishMma i values ra rb)) (hn : X.async.mmaDone i=false)
    (hab : ∀ isB q loc, X.MmaFootprint i isB q loc → ∀ w a bs, X.MemWrites w a bs →
      a.Covers loc → ByteCausality L X loc w (.async i (.mmaRead isB q)) →
      match mmaReadSource ra rb isB q with
      | none => False
      | some w' => ¬ ByteCausality L X loc w' w) :
    Hidden L
      (X.finishMma i values ra rb) := by
  intro e a bs k w target bytes hr hk hw hc hv
  have hw' := finishMma_memWrites.mp hw
  have reflect {loc e f} (h : ByteCausality L (X.finishMma i values ra rb) loc e f) :
      ByteCausality L X loc e f :=
    ByteCausality.reflect_of_same_tr hle rfl hX.tma.2.1 hX.tcCommit
      (fun h => (finishMma_modelCausality hX.tcCommit hn).mp h) (fun h => h) h
  have hv' := reflect hv
  rcases finishMma_reads hr with hold | ⟨isB, q, b, rfl, hf, hsize, _, rfl⟩
  · rw [hle.2.1 e k ⟨a, bs, hold⟩]
    have hh := hX.hidden e a bs k w target bytes hold hk hw' hc hv'
    cases hs : X.rf e k with
    | none => rw [hs] at hh; exact hh
    | some w' =>
      rw [hs] at hh
      exact fun h => hh (reflect h)
  · have hk0 : k = 0 := by omega
    subst k
    have hh := hab isB q a.loc hf w target bytes hw' (by simpa [Loc.at] using hc)
      (by simpa [Loc.at] using hv')
    have hsrc : (X.finishMma i values ra rb).rf (.async i (.mmaRead isB q)) 0 =
        mmaReadSource ra rb isB q := by
      simp only [Execution.finishMma, and_self, ↓reduceIte]
      cases isB <;> rfl
    rw [hsrc]
    cases hs : mmaReadSource ra rb isB q with
    | none => rw [hs] at hh; exact hh
    | some w' =>
      rw [hs] at hh
      exact fun h => hh (by simpa [Loc.at] using reflect h)

end
end PTX
end

section
/-! # Operands of a pending MMA from the writes it reads

A proof tool. To complete an MMA that has not read its operands, choose for each byte of its
`nA`-byte operand A and `nB`-byte operand B a write covering it (`ByteSource`); the operands are
those writes' bytes (`newOperands`) and their read sources the writes (`newSource`). The reads
then satisfy RF (`newOperands_rf`), and they are coherent when every other write of a byte is
ordered before its source or after the read (`newOperands_hidden`). -/

namespace PTX.MmaSources
open PTX AsyncCopy
noncomputable section
set_option maxRecDepth 65536
variable {nA nB : Nat}

/-- A write covering a byte, as the read source of an operand byte. -/
structure ByteSource (X : Execution) where
  loc : Loc
  ref : Ref
  access : Acc
  bytes : List Byte
  write : X.MemWrites ref access bytes
  cover : access.Covers loc

def newOperands {X : Execution}
    (source : (isB : Bool) → Fin (if isB then nB else nA) → ByteSource X) : MmaOperands :=
  ⟨List.ofFn (n := nA) fun k =>
      wbyte (source false k).access (source false k).bytes (source false k).loc,
   List.ofFn (n := nB) fun k =>
      wbyte (source true k).access (source true k).bytes (source true k).loc⟩

def newSource {X : Execution} (source : (isB : Bool) → Fin (if isB then nB else nA) → ByteSource X)
    (isB : Bool) (k : Nat) : Option Ref :=
  if hk : k < (if isB then nB else nA) then some (source isB ⟨k,hk⟩).ref else none

/-- An operand byte of an issue has one footprint location: an MMA's operand layout, or the byte
of the copy's CTA that the byte index selects. -/
theorem mmaFootprint_loc_unique {X : Execution} {i : EvId} {isB : Bool} {k : Nat}
    {l l' : Loc} (h : X.MmaFootprint i isB k l) (h' : X.MmaFootprint i isB k l') : l=l' := by
  rcases h with ⟨d,s,acc,mask,⟨pc,hi⟩,hl⟩ | ⟨c,n,cta,⟨pc,hi⟩,-,hc,hn,hl⟩ <;>
    rcases h' with ⟨d',s',acc',mask',⟨pc',hi'⟩,hl'⟩ | ⟨c',n',cta',⟨pc',hi'⟩,-,hc',hn',hl'⟩ <;>
    cases Option.some.inj (hi.symm.trans hi')
  · exact Option.some.inj (hl.symm.trans hl')
  · subst hn hn'
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    exact Option.some.inj (hl.symm.trans hl')

/-- Both new arrays have the actual production byte extent. -/
theorem newOperands_lengths {X : Execution}
    (source : (isB : Bool) → Fin (if isB then nB else nA) → ByteSource X) :
    (newOperands source).a.length=nA ∧ (newOperands source).b.length=nB := by
  exact ⟨List.length_ofFn,List.length_ofFn⟩

/-- Actual sources provide exactly the fresh-read obligation required by
finishMma_rf; source byte values may remain opaque at this point. -/
theorem newOperands_rf_sources {X : Execution} {i : EvId}
    (source : (isB : Bool) → Fin (if isB then nB else nA) → ByteSource X)
    (hfoot : ∀isB k,X.MmaFootprint i isB k.val (source isB k).loc) :
    ∀isB k loc value, X.MmaFootprint i isB k loc →
      mmaReadValue (newOperands source) isB k=some value →
      ∃w a bs,mmaReadSource (newSource source false) (newSource source true) isB k=some w ∧
        X.MemWrites w a bs ∧ a.Covers loc ∧ value=wbyte a bs loc := by
  intro isB k loc value hf hv
  have hk : k < (if isB then nB else nA) := by
    obtain ⟨hsome,_⟩ := List.getElem?_eq_some_iff.mp hv
    have hlen : (if isB then (newOperands source).b else (newOperands source).a).length =
        (if isB then nB else nA) := by
      cases isB
      · exact List.length_ofFn
      · exact List.length_ofFn
    change k<(if isB then (newOperands source).b else (newOperands source).a).length at hsome
    omega
  let entry := source isB ⟨k,hk⟩
  have hloc : loc=entry.loc := mmaFootprint_loc_unique hf (hfoot isB ⟨k,hk⟩)
  have hvalue : value=wbyte entry.access entry.bytes entry.loc := by
    cases isB
    · have hk' : k < nA := hk
      simpa [mmaReadValue,newOperands,List.getElem?_ofFn,hk',entry] using hv.symm
    · have hk' : k < nB := hk
      simpa [mmaReadValue,newOperands,List.getElem?_ofFn,hk',entry] using hv.symm
  refine ⟨entry.ref,entry.access,entry.bytes,?_,entry.write,hloc ▸ entry.cover,?_⟩
  · cases isB
    · have hk' : k < nA := hk
      simp [mmaReadSource,newSource,hk',entry]
    · have hk' : k < nB := hk
      simp [mmaReadSource,newSource,hk',entry]
  · simpa only [hloc] using hvalue

/-- Candidate arrays backed by actual writers satisfy all fresh RF obligations. -/
theorem newOperands_rf {L : Launch} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} {i : EvId} {K : Kernel} (hX : Consistent L K A mem0 X)
    (source : (isB : Bool) → Fin (if isB then nB else nA) → ByteSource X)
    (hle : X.le
      (X.finishMma i (newOperands source) (newSource source false) (newSource source true)))
    (hfoot : ∀isB k,X.MmaFootprint i isB k.val (source isB k).loc) :
    RfWf mem0
      (X.finishMma i (newOperands source) (newSource source false) (newSource source true)) :=
  finishMma_rf hX hle (newOperands_rf_sources source hfoot)

/-- Byte reuse order supplies coherence for the new candidate observations.
No operand observations are assumed to have existed before this extension. -/
theorem newOperands_hidden {L : Launch} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} {i : EvId} {K : Kernel} (hX : Consistent L K A mem0 X)
    (hg : SyncGuarded L K X)
    (source : (isB : Bool) → Fin (if isB then nB else nA) → ByteSource X)
    (hle : X.le
      (X.finishMma i (newOperands source) (newSource source false) (newSource source true)))
    (hn : X.async.mmaDone i=false)
    (hfoot : ∀isB k,X.MmaFootprint i isB k.val (source isB k).loc)
    (hbound : ∀isB k loc,X.MmaFootprint i isB k loc → k < (if isB then nB else nA))
    (horder : ∀isB (k : Fin (if isB then nB else nA)) w a bs,X.MemWrites w a bs →
      a.Covers (source isB k).loc →
      w=(source isB k).ref ∨ modelCausality L X (source isB k).loc w (source isB k).ref ∨
        modelCausality L X (source isB k).loc (.async i (.mmaRead isB k.val)) w) :
    Hidden L
      (X.finishMma i (newOperands source) (newSource source false) (newSource source true)) := by
  apply finishMma_hidden hX hle hn
  intro isB k loc hf w a bs hw hc hv
  have hk := hbound isB k loc hf
  have hloc := mmaFootprint_loc_unique hf (hfoot isB ⟨k,hk⟩)
  rw [hloc] at hc hv ⊢
  have hsrc : mmaReadSource (newSource source false) (newSource source true) isB k=
      some (source isB ⟨k,hk⟩).ref := by
    cases isB
    · have hk' : k < nA := hk
      simp [mmaReadSource,newSource,hk']
    · have hk' : k < nB := hk
      simp [mmaReadSource,newSource,hk']
  rw [hsrc]
  rcases horder isB ⟨k,hk⟩ w a bs hw hc with he | hb | ha
  · subst w
    intro hs
    exact ByteCausality.acyclic hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk _ _ (.single hs)
  · intro hs
    exact ByteCausality.acyclic hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk _ _
      ((Relation.TransGen.single (ByteCausality.direct hb)).tail hs)
  · exact (uncompleted_mma_no_visibility hX.tcCommit hn (p := .mmaRead isB k)
      True.intro ha).elim

end
end PTX.MmaSources
end
