-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Snoc.PlainAsyncExtend
public import Lemmas.Execution.NoAsyncExtension

@[expose] public section

/-! Execution extensions for the fragment without asynchronous instructions. The fragment
hypothesis is proved from each kernel's source; it is not a Core restriction. Async
kernels use their independent effects and object histories instead. -/
namespace PTX
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event}
  {r : Nat → Option AsyncCopy.Ref}

/-- **Appending an instruction to an execution without asynchronous instructions**: no barrier
or shuffle, and no releasing atomic; an exit included. The thread's previous last event is
ready, every read of the appended event has its sources in `X`, and the atomicity of the
extension is given (it holds unchanged unless the event is an atomic read-modify-write,
`AtomicOk.snoc`). -/
theorem consistent_snoc_noAsync {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : X.NoTma) (hg : g < L.threads)
    {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hk : e.kind.isTma = false)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hrel : ∀ a old new, e.kind = .rmw a old new → a.release = false)
    (hlast : LastReady L X g)
    (hrd : ∀ a bs, (X.snoc g e r).MemReads (.thread (g, (X.tr g).length)) a bs →
      NewRead L mem0 X g e r a bs)
    (hatomic : AtomicOk L (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) :=
  consistent_snoc_plain hX hg hrun hl he hk hnb hns hrel hlast hrd
    (noAsync_snoc_obligations hX hn hk hatomic) hasm

theorem exists_maximal {α : Type} {R : α → α → Prop} (htr : ∀ a b c, R a b → R b c → R a c)
    (hirr : ∀ a, ¬ R a a) (P : α → Prop) :
    ∀ (l : List α), (∃ x ∈ l, P x) → ∃ x ∈ l, P x ∧ ∀ y ∈ l, P y → ¬ R x y
  | [], h => by simp at h
  | x :: l, h => by
    by_cases ht : ∃ y ∈ l, P y
    · obtain ⟨m, hm, hPm, hmax⟩ := exists_maximal htr hirr P l ht
      by_cases hx : P x ∧ R m x
      · refine ⟨x, by simp, hx.1, ?_⟩
        intro y hy hPy hxy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hirr _ hxy
        · exact hmax y hy hPy (htr _ _ _ hx.2 hxy)
      · refine ⟨m, by simp [hm], hPm, ?_⟩
        intro y hy hPy hmy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx ⟨hPy, hmy⟩
        · exact hmax y hy hPy hmy
    · have hPx : P x := by
        obtain ⟨y, hy, hPy⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hPy
        · exact absurd ⟨y, hy, hPy⟩ ht
      refine ⟨x, by simp, hPx, ?_⟩
      intro y hy hPy hxy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hirr _ hxy
      · exact ht ⟨y, hy, hPy⟩

theorem mem_events {v : EvId} (h1 : v.1 < L.threads) (h2 : v.2 < (X.tr v.1).length) :
    v ∈ X.events L := by
  unfold Execution.events
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨v.1, h1, v.2, h2, rfl⟩

/-- The byte that the write `w` (a store or the write of an atomic) stores at `l`. -/
def byteOf (X : Execution) (w : EvId) (l : Loc) : Option Byte :=
  match X.get w with
  | some ⟨_, .wr a bs⟩ => wbyte a bs l
  | some ⟨_, .rmw a _ (some bs)⟩ => wbyte a bs l
  | _ => none

theorem byteOf_of_memWrites {w : EvId} {a : Acc} {bs : List Byte} (l : Loc)
    (h : X.MemWrites (.thread w) a bs) : byteOf X w l = wbyte a bs l := by
  rcases h with ⟨pc, hp⟩ | ⟨old, pc, hp⟩ <;> simp only [byteOf, hp]

/-- A thread in a kernel without async instructions can always perform its next
ordinary read. Sources are chosen from causally maximal visible writes, or W0. -/
theorem read_extend {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : X.NoTma) (hg : g < L.threads) {t t1 : TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    {a : Acc} {kf : List (Option Byte) → TState} (hm : out K A L g t1 = .ev (.read a kf))
    (hacquire : a.acquire = false) (hlast : LastReady L X g)
    (hasm : ∀ bs r, ∀ a' ∈ A, a'.wf L mem0 (X.snoc g ⟨t1.pc, .rd a bs⟩ r)) :
    ∃ bs r, Consistent L K A mem0 (X.snoc g ⟨t1.pc, .rd a bs⟩ r) := by
  classical
  have ha := hn.emptyAsync hX
  let n : EvId := (g, (X.tr g).length)
  let Y0 := X.snoc g ⟨t1.pc, .rd a []⟩ (fun _ => none)
  let P : Nat → EvId → Prop := fun k w =>
    ∃ a' bs', X.MemWrites (.thread w) a' bs' ∧ a'.Covers (a.loc.at k) ∧ baseCausality L Y0 w n
  let Max : Nat → EvId → Prop := fun k w =>
    w ∈ X.events L ∧ P k w ∧ ∀ y ∈ X.events L, P k y → ¬ Relation.TransGen (baseCausality L X) w y
  let rr : Nat → Option EvId := fun k => if h : ∃ w, Max k w then some (Classical.choose h) else
    none
  let r : Nat → Option AsyncCopy.Ref := fun k => (rr k).map .thread
  let bs : List (Option Byte) := (List.range a.size).map fun k =>
    match rr k with
    | none => (mem0 (a.loc.at k)).map (fun c => c.getD (X.initial (a.loc.at k)))
    | some w => byteOf X w (a.loc.at k)
  have hbs : ∀ k < a.size, bs[k]? = some (match rr k with
      | none => (mem0 (a.loc.at k)).map (fun c => c.getD (X.initial (a.loc.at k)))
      | some w => byteOf X w (a.loc.at k)) := by
    intro k hk; simp [bs, List.getElem?_map, List.getElem?_range hk]
  have hwev : ∀ {w a' bs'}, X.MemWrites (.thread w) a' bs' → w ∈ X.events L := by
    intro w a' bs' hw
    have h2 := memWrites_thread_lt hw
    refine mem_events ?_ h2
    by_contra h1; rw [hX.outside w.1 (by omega)] at h2; simp at h2
  have hstage : ∀ n, ¬ Relation.TransGen (stageCausality L X) n n := fun n h =>
    hX.object (.tmem 0) n (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ h)
  have hmax : ∀ k w a' bs', X.MemWrites (.thread w) a' bs' → a'.Covers (a.loc.at k) →
      baseCausality L Y0 w n → ∃ m, Max k m := by
    intro k w a' bs' hw hc hwn
    obtain ⟨m, hm1, hm2, hm3⟩ := exists_maximal (R := Relation.TransGen (baseCausality L X))
      (fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2) (fun _ => vis_chain_irrefl hstage)
      (P k) (X.events L) ⟨w, hwev hw, a', bs', hw, hc, hwn⟩
    exact ⟨m, hm1, hm2, hm3⟩
  have newRead : NewRead L mem0 X g ⟨t1.pc, .rd a bs⟩ r a bs := by
    refine ⟨by simp [bs], fun k hk => ?_, fun k w a' bs' hk hw hc hwn => ?_⟩
    · rw [hbs k hk]
      by_cases h : ∃ w, Max k w
      · have hrr : rr k = some (Classical.choose h) := dite_eq_left h
        simp only [r, hrr, Option.map_some]
        obtain ⟨_, ⟨a', bs', hw, hc, _⟩, _⟩ := Classical.choose_spec h
        exact ⟨a', bs', hw, hc, by rw [byteOf_of_memWrites _ hw]⟩
      · have hrr : rr k = none := dite_eq_right h
        simp only [r, hrr, Option.map_none]
        intro c hc; simp [hc, Execution.initialByte]
    · have hnoMma {Y : Execution} (h : Y.NoTma) : ∀ i d spec acc mask,
          ¬ Y.MmaIssue i d spec acc mask := by
        rintro i d spec acc mask ⟨pc, issue⟩
        exact Bool.noConfusion (h i pc _ issue)
      have hnoCp {Y : Execution} (h : Y.NoTma) : ∀ i spec, ¬ Y.CpIssue i spec := by
        rintro i spec ⟨pc, issue⟩
        exact Bool.noConfusion (h i pc _ issue)
      have hsnoc := hn.snoc (g := g) (r := r) (e := ⟨t1.pc, .rd a bs⟩)
        (show a.acquire = false from hacquire)
      have hold := (ByteCausality.direct_iff_of_no_operand (hnoMma hsnoc) (hnoCp hsnoc)).mp hwn
      obtain ⟨w, rfl, -⟩ := Execution.NoTma.memWrites_thread ha hw
      have hwn0 : baseCausality L Y0 w n := by
        change baseCausality L (X.snoc g ⟨t1.pc, .rd a []⟩ (fun _ => none)) w n
        rw [baseCausality_snoc_eq (e := ⟨t1.pc, .rd a []⟩) (e' := ⟨t1.pc, .rd a bs⟩)
          (r := fun _ => none) (r' := r) rfl rfl hacquire hacquire rfl]
        exact hsnoc.modelCausality_thread.mp hold
      have hex := hmax k w a' bs' hw hc hwn0
      have hrr : rr k = some (Classical.choose hex) := dite_eq_left hex
      simp only [r, hrr, Option.map_some]
      exact fun h => (Classical.choose_spec hex).2.2 w (hwev hw) ⟨a', bs', hw, hc, hwn0⟩
        (.single (hn.modelCausality_thread.mp
          ((ByteCausality.direct_iff_of_no_operand (hnoMma hn) (hnoCp hn)).mp h)))
  have hrd : ∀ a0 bs0, (X.snoc g ⟨t1.pc, .rd a bs⟩ r).MemReads (.thread (g, (X.tr g).length))
      a0 bs0 → NewRead L mem0 X g ⟨t1.pc, .rd a bs⟩ r a0 bs0 := by
    intro a0 bs0 h
    rcases h with ⟨pc, hp⟩ | ⟨nw, pc, hp⟩ <;> rw [snoc_get_new] at hp <;>
      have hkd := congrArg Event.kind (Option.some.inj hp)
    · simp only [Kind.rd.injEq] at hkd
      obtain ⟨rfl, rfl⟩ := hkd
      exact newRead
    · cases hkd
  have hnr : ∀ a' old new, (⟨t1.pc, .rd a bs⟩ : Event).kind ≠ .rmw a' old new := by
    intros; simp
  exact ⟨bs, r, consistent_snoc_noAsync hX hn hg hrun hl (o := some (kf bs))
    ⟨_, hm, bs, by simp [bs], rfl, rfl⟩ hacquire (by simp) (by simp)
    (fun _ _ _ h => by cases h) hlast hrd
    (hX.atomic.snoc hX.store hX.tma.1 hnr) (hasm bs r)⟩

/-- Append an ordinary write, an exit or a local fault, preserving all existing observations. -/
theorem simple_extend {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : X.NoTma) (hg : g < L.threads)
    {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hk : e.kind.isTma = false)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hnr : ∀ a bs, e.kind ≠ .rd a bs) (hnrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (hlast : LastReady L X g)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none))) :
    Consistent L K A mem0 (X.snoc g e (fun _ => none)) := by
  refine consistent_snoc_noAsync hX hn hg hrun hl he hk hnb hns
    (fun a old new h => absurd h (hnrmw a old new)) hlast ?_
    (hX.atomic.snoc hX.store hX.tma.1 hnrmw) hasm
  intro a bs h
  rcases h with ⟨pc, hp⟩ | ⟨nw, pc, hp⟩ <;> rw [snoc_get_new] at hp
  · exact absurd (congrArg Event.kind (Option.some.inj hp)) (hnr a bs)
  · exact absurd (congrArg Event.kind (Option.some.inj hp)) (hnrmw a bs nw)

end
end
end PTX
