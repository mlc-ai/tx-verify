-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcExecution
public import Lemmas.Async.ReadReuse
public import Lemmas.Clc.ClcCompleteConsistentReadFrame

@[expose] public section

/-! Actual CLC response reads through reused shared buffers. The current
replica's own acquire observation and the pipeline's byte-specific reuse order
identify the source. No global unique-writer or safety assumption is used. -/
namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- An actual CLC instruction fixes its specification and target list. -/
theorem Execution.ClcIssue.unique {i : EvId} {s t : Clc.Spec} {cs ds : List Nat}
    (h : X.ClcIssue i s cs) (h' : X.ClcIssue i t ds) : s = t ∧ cs = ds := by
  obtain ⟨pc,hp⟩ := h
  obtain ⟨pc',hp'⟩ := h'
  have he : (⟨pc,.clcIssue s cs⟩ : Event) = ⟨pc',.clcIssue t ds⟩ :=
    Option.some.inj (hp.symm.trans hp')
  cases he
  exact ⟨rfl,rfl⟩

/-- The matching replica observation supplies its exact actual response write,
including the opaque request identity and arbitration result. -/
theorem AsyncCopy.AsyncObserved.clc_response_write (hc : ClcOk L X)
    {i waiter : EvId} {c : Nat} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) {ws : MbarScope}
    (ho : AsyncCopy.AsyncObserved X i (.notify (.cta c)) waiter true ws) :
    ∃ r, (X.clc i).resolved = some r ∧ Clc.Result L i X.clcState r ∧
      X.MemWrites (.async i (.write (.cta c)))
        {loc := {s.response with cta := c},size := 16} (Value.clc r).toBytes := by
  obtain ⟨a,bs,hw,_,r,hr,hresult,hbytes⟩ := ho.clc_completed hc
  have hacc : a = {loc := {s.response with cta := c},size := 16} := by
    obtain ⟨t,ts,ht,_,_,_,_,ha,_⟩ := hw
    obtain ⟨hst,_⟩ := hi.unique ht
    simpa only [hst] using ha
  exact ⟨r,hr,hresult,by simpa only [hacc,hbytes] using hw⟩

/-- A completion publishes only the actual replica response's covered bytes.
The ordinary happens-before chain begins at that matching acquire wait. -/
theorem AsyncCopy.AsyncObserved.clc_vis_response {i waiter consumer : EvId} {c : Nat}
    {ws : MbarScope} (ho : AsyncCopy.AsyncObserved X i (.notify (.cta c)) waiter true ws)
    {dst : Acc} {bytes : List Byte} {l : Loc}
    (hw : X.MemWrites (.async i (.write (.cta c))) dst bytes) (hcover : dst.Covers l)
    (hs : ScopesMeet L .cluster i.1 ws waiter.1) (hhb : baseCausality L X waiter consumer) :
    modelCausality L X l (.async i (.write (.cta c))) (.thread consumer) :=
  ⟨⟨dst,true,hw.intent,hcover⟩,waiter,.inr ⟨ws,ho,hs⟩,.inl hhb⟩

/-- A 16-byte response read gets the matching actual CLC payload. Other
covering writers may exist, including every later use of this shared buffer;
the protocol orders each one before this response or after the consuming read. -/
theorem AsyncCopy.AsyncObserved.clc_read_bytes_of_ordered_reuse (hX : Consistent L K A mem0 X)
    {i waiter consumer : EvId} {c : Nat} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) {ws : MbarScope}
    (ho : AsyncCopy.AsyncObserved X i (.notify (.cta c)) waiter true ws)
    {src : Acc} {bs : List (Option Byte)} (hr : X.MemReads (.thread consumer) src bs)
    (hfoot : src.SameFootprint {loc := {s.response with cta := c},size := 16})
    (hs : ScopesMeet L .cluster i.1 ws waiter.1) (hhb : baseCausality L X waiter consumer)
    (horder : ∀ k < src.size, ∀ other footprint bytes,
      X.MemWrites other footprint bytes → footprint.Covers (src.loc.at k) →
      other = .async i (.write (.cta c)) ∨
        modelCausality L X (src.loc.at k) other (.async i (.write (.cta c))) ∨
          modelCausality L X (src.loc.at k) (.thread consumer) other) :
    ∃ r, (X.clc i).resolved = some r ∧ Clc.Result L i X.clcState r ∧
      bs = (Value.clc r).toBytes.map some := by
  obtain ⟨r,hresolved,hresult,hw⟩ := ho.clc_response_write hX.clc hi
  refine ⟨r,hresolved,hresult,?_⟩
  have hlength := (hX.rf (.thread consumer) src bs hr).1
  have hsize : src.size = 16 := hfoot.2
  have hloc : src.loc = {s.response with cta := c} := hfoot.1
  have hbytes : (Value.clc r).toBytes.length = 16 := by simp [Value.toBytes,Value.bytes]
  apply List.ext_getElem?
  intro k
  by_cases hk : k < src.size
  · have hcover : ({loc := {s.response with cta := c},size := 16} : Acc).Covers
        (src.loc.at k) := by
      exact (hfoot.covers _).mp (Acc.covers_at hk)
    have hv := ho.clc_vis_response hw hcover hs hhb
    have hvalue := read_byte_of_ordered_reuse hX hr hk hw hcover hv (horder k hk)
    have hk16 : k < 16 := by omega
    have hget : (Value.clc r).toBytes[k]? = some ((Value.clc r).byteAt k) := by
      simp [Value.toBytes,Value.bytes,List.getElem?_range hk16]
    simpa only [wbyte,hloc,Loc.at,Nat.add_sub_cancel_left,List.getElem?_map,hget,
      Option.map_some] using hvalue
  · rw [List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by simp only [List.length_map,hbytes]; omega)]

/-- In addition to the exact bytes, scalar b128 reconstruction preserves the
same opaque CLC response and its request identity. -/
theorem AsyncCopy.AsyncObserved.clc_read_rebuild_of_ordered_reuse (hX : Consistent L K A mem0 X)
    {i waiter consumer : EvId} {c : Nat} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) {ws : MbarScope}
    (ho : AsyncCopy.AsyncObserved X i (.notify (.cta c)) waiter true ws)
    {src : Acc} {bs : List (Option Byte)} (hr : X.MemReads (.thread consumer) src bs)
    (hfoot : src.SameFootprint {loc := {s.response with cta := c},size := 16})
    (hs : ScopesMeet L .cluster i.1 ws waiter.1) (hhb : baseCausality L X waiter consumer)
    (horder : ∀ k < src.size, ∀ other footprint bytes,
      X.MemWrites other footprint bytes → footprint.Covers (src.loc.at k) →
      other = .async i (.write (.cta c)) ∨
        modelCausality L X (src.loc.at k) other (.async i (.write (.cta c))) ∨
          modelCausality L X (src.loc.at k) (.thread consumer) other) :
    ∃ r, (X.clc i).resolved = some r ∧ Clc.Result L i X.clcState r ∧
      bs = (Value.clc r).toBytes.map some ∧ rebuild 3 bs = .ok (.clc r) := by
  obtain ⟨r,hresolved,hresult,hbytes⟩ :=
    ho.clc_read_bytes_of_ordered_reuse hX hi hr hfoot hs hhb horder
  exact ⟨r,hresolved,hresult,hbytes,rebuild_clc_of_bytes hbytes⟩


end
end PTX
