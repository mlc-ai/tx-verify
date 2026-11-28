-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchEqual
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.RoundOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchSize
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchLater
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Publish
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Reuse
import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Prologue.Export.Publish
import Lemmas.Kernel.Safety.HandoffPhased

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame

private theorem ord_bar {X : Execution} {h i pc c md}
    (get : X.get (h,i)=some ⟨pc,.bar 0 c md⟩) : barOrdinal X h (i+1)=barOrdinal X h i+1 := by
  unfold barOrdinal
  rw [List.take_add_one,show (X.tr h)[i]?=_ from get,List.countP_append]
  rfl

/-- A softmax store and the scratch load of the next sync: the round of the store precedes
the load, or the load's round precedes the store, never the same round's later store. -/
private theorem round_pair {Q L m X h u g k dst ys a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (agree : ∀ n, StoreAgree L X n) (store : X.get (h,u)=some ⟨2250,.wr dst ys⟩)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩) (cta : h/L.block=g/L.block) :
    baseCausality L X (h,u) (g,k) ∨ baseCausality L X (g,k) (h,u) := by
  have lh := Softmax.Export.data_site hp hX store (by simp) (by dsimp; decide) (by dsimp; decide)
  have lg := Softmax.Export.data_site hp hX read (by simp) (by dsimp; decide) (by dsimp; decide)
  rcases Nat.lt_trichotomy (barOrdinal X h u) (barOrdinal X g k) with lt|eq|gt
  · exact .inl (round_before hp hX store read (by simp) rfl rfl (by simp [Execution.isBarId])
      lh lg cta lt)
  · exfalso
    obtain ⟨j,rfl,sync⟩ := Softmax.Export.read_sync hp hX read
    have step := ord_bar (X := X) sync
    have uni := rescale_agree_by hp hX hf (fun m _ => agree m) sync (by simp) rfl rfl lg
    have pub := scratch_next_publication hp hX hf read
      (fun h' ch lh' n' lt' => uni h' g ch lh' rfl lg n' lt')
    have below : barOrdinal X g j<barOrdinal X h u := by omega
    obtain ⟨i,p,c,md,ilt,eh,ord⟩ := Frame.nth_bar (X:=X) (g:=h) (f:=u) (q:=barOrdinal X g j)
      (id:=0) below
    obtain ⟨rfl,-⟩ := Lib.recorded_bar hX hp.block eh
    have two := pub h i p c cta lh eh ord
    subst two
    obtain ⟨j',lo,hi,mid⟩ := Softmax.Export.scratch_separated hp hX (show X.IsBarrier (h,i) 0 c 2251
      from eh) ilt store
    have e1 := Flow.countP_take_mono (Execution.isBarId 0) (X.tr h) (show i+1≤j' by omega)
    have e2 := Flow.countP_take_mono (Execution.isBarId 0) (X.tr h) (show j'+1≤u by omega)
    have e3 := ord_bar (X := X) (show X.get (h,j')=some ⟨2241,.bar 0 (some 128) .sync⟩ from mid)
    have e4 := ord_bar (X := X) eh
    change barOrdinal X h (i+1)≤barOrdinal X h j' at e1
    change barOrdinal X h (j'+1)≤barOrdinal X h u at e2
    have e5 : barOrdinal X h i=barOrdinal X g j := ord
    omega
  · exact .inr (round_before hp hX read store (by simp) rfl rfl (by simp [Execution.isBarId])
      lg lh cta.symm gt)

/-- A store of a publication generation precedes each event with more barrier-1 events before it. -/
private theorem phase_before {Q L m X h u g k pw p dst ys ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (store : X.get (h,u)=some ⟨pw,.wr dst ys⟩) (ph : Export.publishedAt pw=some p)
    (later : X.get (g,k)=some ev) (cta : h/L.block=g/L.block)
    (lt : p<((X.tr g).take k).countP (Execution.isBarId 1)) :
    baseCausality L X (h,u) (g,k) := by
  apply publication_handoff hp hX h g u k ⟨lt_of_get hX store,lt_of_get hX later,cta⟩
    (List.getElem?_eq_some_iff.mp later).1
  change ((X.tr h).take (u+1)).countP _<((X.tr g).take k).countP _
  rw [List.take_add_one,show (X.tr h)[u]?=_ from store,List.countP_append,
    Export.publication_store hp hX store ph]
  exact lt

/-- A count-pair or scratch store and a load of the same word are ordered. -/
private theorem write_read {Q L m X h u g k pw pr dst ys a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (agree : ∀ n, StoreAgree L X n) (store : X.get (h,u)=some ⟨pw,.wr dst ys⟩)
    (hw : pw=571 ∨ pw=2250) (read : X.get (g,k)=some ⟨pr,.rd a bs⟩)
    (hr : pr=2252 ∨ pr=2345 ∨ pr=2423) (cta : h/L.block=g/L.block) :
    baseCausality L X (h,u) (g,k) ∨ baseCausality L X (g,k) (h,u) := by
  rcases hw with rfl|rfl
  · rcases hr with rfl|rfl|rfl
    · refine .inl (phase_before hp hX store (p:=0) rfl read cta ?_)
      have := Export.after_initialization hp hX read (fun _ => nofun) (by simp [Export.afterInit])
      omega
    · exact .inl (publish_before_read hp hX store (.inr rfl) read (.inr (.inl rfl)) cta)
    · exact .inl (publish_before_read hp hX store (.inr rfl) read (.inr (.inr rfl)) cta)
  · rcases hr with rfl|rfl|rfl
    · exact round_pair hp hX hf agree store read cta
    all_goals
      have phase := Export.publication_read hp hX read (by simp)
      by_cases one : ((X.tr g).take k).countP (Execution.isBarId 1)=1
      · exact .inr (first_read_before_reuse hp hX read one store (.inl rfl) cta.symm)
      · exact .inl (phase_before hp hX store (p:=2) rfl read cta (by omega))

private theorem same_bytes {L m X h u t v dst ys acc zs pc pc'}
    (hX : Consistent L kernel Assumptions.all m X) (one : X.get (h,u)=some ⟨pc,.wr dst ys⟩)
    (two : X.get (t,v)=some ⟨pc',.wr acc zs⟩) (fp : dst.SameFootprint acc) (eq : ys=zs) :
    SameValueWrites X (.thread (h,u)) (.thread (t,v)) dst acc := by
  refine ⟨.inr (.inl ⟨_,⟨_,one⟩,rfl⟩),.inr (.inl ⟨_,⟨_,two⟩,rfl⟩),fp,fun bs bs' w1 w2 => ?_⟩
  rcases Lib.write_kinds hX w1 with ⟨i,p1,hi,g1⟩|⟨_,_,_,_,_,_,hi,_⟩
  swap
  · cases hi
  rcases Lib.write_kinds hX w2 with ⟨j,p2,hj,g2⟩|⟨_,_,_,_,_,_,hj,_⟩
  swap
  · cases hj
  cases hi
  cases hj
  obtain ⟨-,k1⟩ := Event.mk.inj (Option.some.inj (one.symm.trans g1))
  obtain ⟨-,k2⟩ := Event.mk.inj (Option.some.inj (two.symm.trans g2))
  rw [← (Kind.wr.inj k1).2,← (Kind.wr.inj k2).2,eq]

/-- Two stores of different lanes at one scratch word are ordered, or write the same bytes. -/
private theorem write_write {Q L m X h u t v pw pt dst ys acc zs l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (agree : ∀ n, StoreAgree L X n) (equal : WarpStoresEqual L X)
    (one : X.get (h,u)=some ⟨pw,.wr dst ys⟩) (hw : pw=571 ∨ pw=2250)
    (two : X.get (t,v)=some ⟨pt,.wr acc zs⟩) (ht : pt=571 ∨ pt=2250) (fp : dst.SameFootprint acc)
    (hit : dst.Covers l) (hit' : acc.Covers l) (cta : h/L.block=t/L.block) :
    baseCausality L X (h,u) (t,v) ∨ baseCausality L X (t,v) (h,u) ∨
      SameValueWrites X (.thread (h,u)) (.thread (t,v)) dst acc := by
  rcases hw with rfl|rfl <;> rcases ht with rfl|rfl
  · right; right
    obtain ⟨j,_,_,wl,val⟩ := Prologue.Export.pair_bytes hp hX one
    obtain ⟨j',_,_,wl',val'⟩ := Prologue.Export.pair_bytes hp hX two
    have loc := fp.1
    rw [wl,wl'] at loc
    obtain ⟨-,c,addr⟩ := Loc.mk.inj loc
    have same : j=j' := Fin.ext (by omega)
    subst same
    rw [cta] at val
    exact same_bytes hX one two fp (val.trans val'.symm)
  · exact .inl (pair_before_scratch hp hX one two cta)
  · exact .inr (.inl (pair_before_scratch hp hX two one cta.symm))
  · have lh := Softmax.Export.data_site hp hX one (by simp) (by dsimp; decide) (by dsimp; decide)
    have lt := Softmax.Export.data_site hp hX two (by simp) (by dsimp; decide) (by dsimp; decide)
    rcases Nat.lt_trichotomy (barOrdinal X h u) (barOrdinal X t v) with lo|eq|gt
    · exact .inl (round_before hp hX one two (by simp) rfl rfl (by simp [Execution.isBarId])
        lh lt cta lo)
    · right; right
      obtain ⟨wl,ws⟩ := Softmax.Export.scratch_store hp hX one
      obtain ⟨wl',ws'⟩ := Softmax.Export.scratch_store hp hX two
      obtain ⟨_,c1,lo1,hi1⟩ := hit
      obtain ⟨_,c2,lo2,hi2⟩ := hit'
      rw [wl] at lo1 hi1
      rw [wl'] at lo2 hi2
      rw [ws] at hi1
      rw [ws'] at hi2
      dsimp only at lo1 lo2 hi1 hi2
      exact same_bytes hX one two fp (stores_equal hp hX hf equal (fun n _ => agree n) one two cta
        (by omega) eq)
    · exact .inr (.inl (round_before hp hX two one (by simp) rfl rfl (by simp [Execution.isBarId])
        lt lh cta.symm gt))

private theorem thread_access {X : Execution} {g k a w}
    (h : (w=true ∧ ∃ pc bs, X.get (g,k)=some ⟨pc,.wr a bs⟩ ∧ (pc=571 ∨ pc=2250)) ∨
      (w=false ∧ ∃ pc bs, X.get (g,k)=some ⟨pc,.rd a bs⟩ ∧ (pc=2252 ∨ pc=2345 ∨ pc=2423))) :
    X.Access (g,k) a w := by
  rcases h with ⟨rfl,pc,bs,get,_⟩|⟨rfl,pc,bs,get,_⟩
  · exact .inr (.inl ⟨bs,⟨pc,get⟩,rfl⟩)
  · exact .inl ⟨bs,⟨pc,get⟩,rfl⟩

/-- **The conflicting accesses of the count pair and the scratch words are ordered**, but for two
stores of one value. -/
theorem scratch_ordered {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (equal : WarpStoresEqual L X) :
    ByteOrdered L X fun l => Iface.InCount L l ∨ Iface.InScratch L l := by
  have agree := store_agree hp hX hf equal
  rintro e f a b l ⟨hne,we,wf,he,hfe,hw,-⟩ ca cb reg ne
  have ⟨sp,lo,hi⟩ : l.space=.shared ∧ L.sharedBase+212992≤l.addr ∧ l.addr<L.sharedBase+213008 := by
    rcases reg with ⟨sp,lo,hi⟩|⟨sp,lo,hi⟩ <;> exact ⟨sp,by omega,by omega⟩
  obtain ⟨g,k,-,rfl,-,-,ctaA,kindA⟩ := scratch_access hp hX hf he ca sp lo hi
  obtain ⟨g',k',-,rfl,-,-,ctaB,kindB⟩ := scratch_access hp hX hf hfe cb sp lo hi
  have fp := scratch_footprint hp hX hf he hfe ca cb reg
  have cta : g/L.block=g'/L.block := ctaA.symm.trans (ca.2.1.symm.trans (cb.2.1.trans ctaB))
  have accA := thread_access kindA
  have accB := thread_access kindB
  by_cases lane : g=g'
  · subst lane
    have kne : k≠k' := fun h => hne (by subst h; rfl)
    rcases Nat.lt_or_gt_of_ne kne with lt|gt
    · exact .inl (.direct (.inl (.single (.inl (po_of_overlap accA accB rfl lt ⟨l,ca,cb⟩)))))
    · exact .inr (.direct (.inl (.single (.inl (po_of_overlap accB accA rfl gt ⟨l,cb,ca⟩)))))
  rcases kindA with ⟨rfl,pc,bs,gA,pA⟩|⟨rfl,pc,bs,gA,pA⟩ <;>
    rcases kindB with ⟨rfl,pc',bs',gB,pB⟩|⟨rfl,pc',bs',gB,pB⟩
  · rcases write_write hp hX hf agree equal gA pA gB pB fp ca cb cta with h|h|h
    · exact .inl (.direct (.inl h))
    · exact .inr (.direct (.inl h))
    · exact (ne h).elim
  · rcases write_read hp hX hf agree gA pA gB pB cta with h|h
    · exact .inl (.direct (.inl h))
    · exact .inr (.direct (.inl h))
  · rcases write_read hp hX hf agree gB pB gA pA cta.symm with h|h
    · exact .inr (.direct (.inl h))
    · exact .inl (.direct (.inl h))
  · simp at hw

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
