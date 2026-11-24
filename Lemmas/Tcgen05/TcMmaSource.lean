-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncOrder
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Tmem.TmemStore
public import Lemmas.Tcgen05.TcMmaReadMono
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Tcgen05.TcCopyCtas

@[expose] public section

/-! # The value a Tensor Memory cell holds is determined

A proof tool. Every order between Tensor Memory writes (`WriteBefore`: observed completion,
pipeline, store completion, copy pipeline) is a tcgen05 order path (`TcStep`), so in a
consistent execution with guarded synchronization it is asymmetric (`writeBefore_asymm`). Hence the
source of a Tensor Memory read is unique (`readSource_unique`), and the value a write leaves in a
cell is a function of the write and the cell (`wrote_functional`), once each MMA's output layout is
injective in its matrix coordinate (`LayoutInjective`); a copy writes each CTA of its group once
(`cpIssue_ctas_nodup`). The last write of a cell, every other write of which is ordered before it
(`LastWrote`), determines one value (`lastWrote_unique`). -/

namespace PTX.TcMma
open PTX AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0}

/-- **Write orders are asymmetric** in a consistent execution whose synchronization is
guarded: each is a tcgen05 order path (`WriteBefore.tcStep`), and these have no cycle
(`tcStep_acyclic`). -/
theorem writeBefore_asymm (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    {x y : EvId} (hxy : WriteBefore L X x y) (hyx : WriteBefore L X y x) : False :=
  tcStep_asymm hX hg hxy.tcStep hyx.tcStep

/-- The source row of a copy is determined by a Tensor Memory lane it writes. -/
theorem lanes_inj {sh : TcCpShape} {r r' lane : Nat} (hr : r < sh.rows) (hr' : r' < sh.rows)
    (h : lane ∈ sh.lanes r) (h' : lane ∈ sh.lanes r') : r = r' := by
  cases sh with
  | s64x128b b =>
    cases b <;> simp only [TcCpShape.lanes, TcCpShape.rows, List.mem_cons, List.not_mem_nil,
      or_false] at h h' hr hr' <;> omega
  | _ =>
    simp only [TcCpShape.lanes, TcCpShape.rows, List.mem_cons, List.not_mem_nil,
      or_false] at h h' hr hr'
    omega

/-- A write leaves its value in a cell it writes. -/
theorem Wrote.tmemWrite {source : EvId} {cell : Cell} {v : Value}
    (h : Wrote L A X source cell v) : TmemWrite L X source cell := by
  rcases h with h | ⟨a, vals, sh, j, ht, hj, hc⟩ |
      ⟨c, k, cta, ops, row, col, lane, hp, hk, -, hr, hcol, hl, hcell, -⟩ | ⟨_, _, hs, -⟩
  · cases h with
    | overwrite hi hp _ _ => exact .inl ⟨_, _, _, _, _, _, hi, hp⟩
    | accumulate hi hp _ _ _ _ => exact .inl ⟨_, _, _, _, _, _, hi, hp⟩
    | accumulateStored hi hp _ _ _ _ => exact .inl ⟨_, _, _, _, _, _, hi, hp⟩
  · exact .inr (.inl ⟨a, vals, sh, j, ht, (List.getElem?_eq_some_iff.mp hj).1, hc⟩)
  · have hrb : 0 < c.shape.rowBytes := by cases c.shape <;> simp [TcCpShape.rowBytes]
    have h4 : 4 * col < c.shape.rowBytes := by
      have : c.shape.rowBytes % 4 = 0 := by cases c.shape <;> simp [TcCpShape.rowBytes]
      omega
    have hdiv : (row * c.shape.rowBytes + 4 * col) / c.shape.rowBytes = row := by
      rw [Nat.mul_comm, Nat.mul_add_div hrb, Nat.div_eq_of_lt h4, Nat.add_zero]
    refine .inr (.inr (.inl ⟨c, cta, row * c.shape.rowBytes + 4 * col, lane, hp,
      List.mem_of_getElem? hk, ?_, by rwa [hdiv], hcell⟩))
    have : row * c.shape.rowBytes + 4 * col < (row + 1) * c.shape.rowBytes := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact lt_of_lt_of_le this (by
      unfold TcCpShape.sourceBytes
      exact Nat.mul_le_mul_right _ hr)
  · exact .inr (.inr (.inr hs.1))

/-- A Tensor Memory read happens before an operation that it is ordered before, other than its
own: by a tcgen05 order path. -/
theorem ReadBefore.tcStep {k : TmemRead} {e w : EvId} (h : ReadBefore L X k e w) (hne : w ≠ e) :
    Relation.TransGen (TcStep L X) e w := by
  cases k with
  | ld => rcases h with h | h
          · exact h.tcStep
          · exact h.tcBefore.tcStep
  | acc => rcases h with h | h | h
           · exact (hne h).elim
           · exact h.tcStep
           · exact h.tcBefore.tcStep
  | a => rcases h with h | h | h | h
         · exact (hne h).elim
         · exact h.tcStep
         · exact h.tcBefore.tcStep
         · exact h.tcBefore.tcStep
  | shift => rcases h with h | h
             · exact (hne h).elim
             · exact h.tcStep

/-- **The source of a Tensor Memory read is unique.** -/
theorem readSource_unique (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    {k : TmemRead} {s s' e : EvId} {cell : Cell}
    (hs : ReadSource L X k s e cell) (hs' : ReadSource L X k s' e cell) : s = s' := by
  by_contra hne
  have h1 : WriteBefore L X s' s := by
    rcases hs.2.2.2.1 s' hs'.2.1 with h | h | h
    · exact absurd h.symm hne
    · exact h
    · exact (tcStep_asymm hX hg (h.tcStep hs'.1) hs'.2.2.1.tcStep).elim
  have h2 : WriteBefore L X s s' := by
    rcases hs'.2.2.2.1 s hs.2.1 with h | h | h
    · exact absurd h hne
    · exact h
    · exact (tcStep_asymm hX hg (h.tcStep hs.1) hs.2.2.1.tcStep).elim
  exact writeBefore_asymm hX hg h1 h2

/-- An event has one MMA issue. -/
theorem mmaIssue_params {i : EvId} {d d' : Nat} {s s' : OperandSpec} {a a' : Bool}
    {m m' : List Nat} (hi : X.MmaIssue i d s a m) (hj : X.MmaIssue i d' s' a' m') :
    d = d' ∧ s = s' ∧ a = a' ∧ m = m' := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', hf⟩ := hj
  have h := Option.some.inj (he.symm.trans hf)
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h
  exact h.2

/-- **A store leaves one value in a cell.** -/
theorem storeValue_functional {st : EvId} {cell : Cell} {v v' : Value}
    (h : StoreValue L X st cell v) (h' : StoreValue L X st cell v') : v = v' := by
  obtain ⟨a, vals, sh, j, ⟨pc, hp⟩, hj, hc⟩ := h
  obtain ⟨a', vals', sh', j', ⟨pc', hp'⟩, hj', hc'⟩ := h'
  have he := Option.some.inj (hp.symm.trans hp')
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at he
  obtain ⟨-, rfl, rfl, rfl⟩ := he
  obtain rfl := tcDataCell_inj (hc.symm.trans hc')
  exact Option.some.inj (hj.symm.trans hj')

/-- **A copy leaves one value in a cell**: its CTAs are distinct (`cpIssue_ctas_nodup`). -/
theorem cpValue_functional (hX : Consistent L K A mem0 X) {cp : EvId} {cell : Cell} {v v' : Value}
    (h : CpValue X cp cell v) (h' : CpValue X cp cell v') : v = v' := by
  obtain ⟨c, k, cta, ops, row, col, lane, ⟨pc, hp⟩, hk, ho, hr, hc, hl, hcell, hw⟩ := h
  obtain ⟨c', k', cta', ops', row', col', lane', ⟨pc', hp'⟩, hk', ho', hr', hc', hl', hcell',
    hw'⟩ := h'
  have he := Option.some.inj (hp.symm.trans hp')
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.cp.injEq] at he
  obtain ⟨-, rfl⟩ := he
  have hops := Option.some.inj (ho.symm.trans ho')
  subst hops
  have hrb : c.shape.rowBytes = 16 ∨ c.shape.rowBytes = 32 := by
    cases c.shape <;> simp [TcCpShape.rowBytes]
  have hcc := hcell.symm.trans hcell'
  simp only [TcCopy.cell, Cell.mk.injEq] at hcc
  obtain ⟨rfl, hlane, hcol⟩ := hcc
  have hlane' : lane = lane' := by omega
  subst hlane'
  have hcol' : col = col' := by
    rcases hrb with hrb | hrb <;> rw [hrb] at hcol hc hc' <;> omega
  subst hcol'
  obtain rfl := lanes_inj hr hr' hl hl'
  have hkk : k = k' := (cpIssue_ctas_nodup hX ⟨pc, hp⟩).eq_of_getElem?_eq
    (List.getElem?_eq_some_iff.mp hk).1 (hk.trans hk'.symm)
  subst hkk
  exact Option.some.inj (hw.symm.trans hw')

/-- An MMA result is written by an MMA issue. -/
theorem Result.mmaIssue {i : EvId} {cell : Cell} {v : Value} (h : Result L A X i cell v) :
    ∃ d s acc mask, X.MmaIssue i d s acc mask := by
  cases h with
  | overwrite hi _ _ _ => exact ⟨_, _, _, _, hi⟩
  | accumulate hi _ _ _ _ _ => exact ⟨_, _, _, _, hi⟩
  | accumulateStored hi _ _ _ _ _ => exact ⟨_, _, _, _, hi⟩

/-- Each MMA's output layout is injective in its matrix coordinate. -/
def LayoutInjective (X : Execution) : Prop :=
  ∀ i d s acc mask, X.MmaIssue i d s acc mask → ∀ row col row' col' cell,
    writeCell s d mask row col = some cell → writeCell s d mask row' col' = some cell →
      row = row' ∧ col = col'

/-- **An MMA leaves one value in a cell**, when its output layout is injective. -/
theorem result_functional (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hinj : LayoutInjective X)
    {i : EvId} {cell : Cell} {v w : Value}
    (hv : Result L A X i cell v) (hw : Result L A X i cell w) : v = w := by
  induction hv generalizing w with
  | @overwrite i d s mask row col cell operands value hi hp hr ha =>
    cases hw with
    | @overwrite _ d' s' mask' row' col' _ operands' value' hi' hp' hr' ha' =>
      obtain ⟨rfl, rfl, -, rfl⟩ := mmaIssue_params hi hi'
      obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ _ hi _ _ _ _ _ hp hp'
      have he := Option.some.inj (hr.symm.trans hr')
      subst he
      exact Except.ok.inj (ha.symm.trans ha')
    | accumulate hi' _ _ _ _ _ => cases (mmaIssue_params hi hi').2.2.1
    | accumulateStored hi' _ _ _ _ _ => cases (mmaIssue_params hi hi').2.2.1
  | @accumulate i d s mask row col cell operands value source old hi hp hr hprior hsource ha ih =>
    cases hw with
    | overwrite hi' _ _ _ => cases (mmaIssue_params hi hi').2.2.1
    | @accumulate _ d' s' mask' row' col' _ operands' value' source' old' hi' hp' hr' hprior'
        hsource' ha' =>
      obtain ⟨rfl, rfl, -, rfl⟩ := mmaIssue_params hi hi'
      obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ _ hi _ _ _ _ _ hp hp'
      obtain rfl := readSource_unique hX hg hsource hsource'
      obtain rfl := ih hprior'
      have he := Option.some.inj (hr.symm.trans hr')
      subst he
      exact Except.ok.inj (ha.symm.trans ha')
    | accumulateStored _ _ _ hstore hsource' _ =>
      obtain rfl := readSource_unique hX hg hsource hsource'
      obtain ⟨a, vals, sh, j, ht, -, -⟩ := hstore
      obtain ⟨_, _, _, _, hpi⟩ := hprior.mmaIssue
      exact (mmaIssue_not_tst hpi ht).elim
  | @accumulateStored i d s mask row col cell operands value source old hi hp hr hstore hsource
      ha =>
    cases hw with
    | overwrite hi' _ _ _ => cases (mmaIssue_params hi hi').2.2.1
    | accumulate _ _ _ hprior' hsource' _ =>
      obtain rfl := readSource_unique hX hg hsource hsource'
      obtain ⟨a, vals, sh, j, ht, -, -⟩ := hstore
      obtain ⟨_, _, _, _, hpi⟩ := hprior'.mmaIssue
      exact (mmaIssue_not_tst hpi ht).elim
    | @accumulateStored _ d' s' mask' row' col' _ operands' value' source' old' hi' hp' hr'
        hstore' hsource' ha' =>
      obtain ⟨rfl, rfl, -, rfl⟩ := mmaIssue_params hi hi'
      obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ _ hi _ _ _ _ _ hp hp'
      obtain rfl := readSource_unique hX hg hsource hsource'
      obtain rfl := storeValue_functional hstore hstore'
      have he := Option.some.inj (hr.symm.trans hr')
      subst he
      exact Except.ok.inj (ha.symm.trans ha')

/-- The `tcgen05` instruction that leaves a value in Tensor Memory: an MMA (0), a store (1), a
copy (2) or a shift (3). -/
private def tcTag : TcKind → Nat
  | .mma .. => 0
  | .st .. => 1
  | .cp _ => 2
  | .shift _ => 3
  | _ => 4

/-- A write of each kind is an event of its tag. -/
private theorem wrote_tag {s : EvId} {cell : Cell} {v : Value} (n : Nat)
    (h : (n = 0 ∧ Result L A X s cell v) ∨ (n = 1 ∧ StoreValue L X s cell v) ∨
      (n = 2 ∧ CpValue X s cell v) ∨ (n = 3 ∧ ShiftValue L A X s cell v)) :
    ∃ pc t, X.get s = some ⟨pc, .tc t⟩ ∧ tcTag t = n := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨_, _, _, _, pc, hp⟩ := h.mmaIssue
    exact ⟨pc, _, hp, rfl⟩
  · obtain ⟨_, _, _, _, ⟨pc, hp⟩, -⟩ := h
    exact ⟨pc, _, hp, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, ⟨pc, hp⟩, -⟩ := h
    exact ⟨pc, _, hp, rfl⟩
  · obtain ⟨_, _, ⟨⟨_, ⟨pc, hp⟩, -⟩, -⟩, -⟩ := h
    exact ⟨pc, _, hp, rfl⟩

/-- Two writes of different kinds are not the same event. -/
private theorem tag_eq {s : EvId} {n n' : Nat}
    (h : ∃ pc t, X.get s = some ⟨pc, .tc t⟩ ∧ tcTag t = n)
    (h' : ∃ pc t, X.get s = some ⟨pc, .tc t⟩ ∧ tcTag t = n') : n = n' := by
  obtain ⟨pc, t, ht, rfl⟩ := h
  obtain ⟨pc', t', ht', rfl⟩ := h'
  rw [ht] at ht'
  cases ht'
  rfl

/-- **An MMA, store or copy leaves one value in a cell.** -/
theorem baseWrote_functional (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hinj : LayoutInjective X) {s : EvId} {cell : Cell} {v v' : Value}
    (h : Result L A X s cell v ∨ StoreValue L X s cell v ∨ CpValue X s cell v)
    (h' : Result L A X s cell v' ∨ StoreValue L X s cell v' ∨ CpValue X s cell v') :
    v = v' := by
  have tR : ∀ {w}, Result L A X s cell w → ∃ pc t, X.get s = some ⟨pc, .tc t⟩ ∧ tcTag t = 0 :=
    fun h => wrote_tag (L := L) (A := A) 0 (.inl ⟨rfl, h⟩)
  have tS : ∀ {w}, StoreValue L X s cell w → ∃ pc t, X.get s = some ⟨pc, .tc t⟩ ∧ tcTag t = 1 :=
    fun h => wrote_tag (L := L) (A := A) 1 (.inr (.inl ⟨rfl, h⟩))
  have tC : ∀ {w}, CpValue X s cell w → ∃ pc t, X.get s = some ⟨pc, .tc t⟩ ∧ tcTag t = 2 :=
    fun h => wrote_tag (L := L) (A := A) 2 (.inr (.inr (.inl ⟨rfl, h⟩)))
  rcases h with h | h | h <;> rcases h' with h' | h' | h'
  · exact result_functional hX hg hinj h h'
  · cases tag_eq (tR h) (tS h')
  · cases tag_eq (tR h) (tC h')
  · cases tag_eq (tS h) (tR h')
  · exact storeValue_functional h h'
  · cases tag_eq (tS h) (tC h')
  · cases tag_eq (tC h) (tR h')
  · cases tag_eq (tC h) (tS h')
  · exact cpValue_functional hX h h'

/-- **A write leaves one value in a cell**, when each MMA's output layout is injective
(`LayoutInjective`). A shift leaves the value of its unique source in the next lane. -/
theorem wrote_functional (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hinj : LayoutInjective X)
    {s : EvId} {cell : Cell} {v v' : Value}
    (h : Wrote L A X s cell v) (h' : Wrote L A X s cell v') : v = v' := by
  have shift_base : ∀ {w w'}, ShiftValue L A X s cell w →
      (Result L A X s cell w' ∨ StoreValue L X s cell w' ∨ CpValue X s cell w') → False := by
    intro w w' hs hb
    have h3 := wrote_tag (L := L) (A := A) 3 (.inr (.inr (.inr ⟨rfl, hs⟩)))
    rcases hb with hb | hb | hb
    · cases tag_eq h3 (wrote_tag (L := L) (A := A) 0 (.inl ⟨rfl, hb⟩))
    · cases tag_eq h3 (wrote_tag (L := L) (A := A) 1 (.inr (.inl ⟨rfl, hb⟩)))
    · cases tag_eq h3 (wrote_tag (L := L) (A := A) 2 (.inr (.inr (.inl ⟨rfl, hb⟩))))
  rcases h with h | h | h | h <;> rcases h' with h' | h' | h' | h'
  · exact baseWrote_functional hX hg hinj (.inl h) (.inl h')
  · exact baseWrote_functional hX hg hinj (.inl h) (.inr (.inl h'))
  · exact baseWrote_functional hX hg hinj (.inl h) (.inr (.inr h'))
  · exact (shift_base h' (.inl h)).elim
  · exact baseWrote_functional hX hg hinj (.inr (.inl h)) (.inl h')
  · exact baseWrote_functional hX hg hinj (.inr (.inl h)) (.inr (.inl h'))
  · exact baseWrote_functional hX hg hinj (.inr (.inl h)) (.inr (.inr h'))
  · exact (shift_base h' (.inr (.inl h))).elim
  · exact baseWrote_functional hX hg hinj (.inr (.inr h)) (.inl h')
  · exact baseWrote_functional hX hg hinj (.inr (.inr h)) (.inr (.inl h'))
  · exact baseWrote_functional hX hg hinj (.inr (.inr h)) (.inr (.inr h'))
  · exact (shift_base h' (.inr (.inr h))).elim
  · exact (shift_base h (.inl h')).elim
  · exact (shift_base h (.inr (.inl h'))).elim
  · exact (shift_base h (.inr (.inr h'))).elim
  · obtain ⟨src, fr, ⟨-, hfr, -, hsrc⟩, hv⟩ := h
    obtain ⟨src', fr', ⟨-, hfr', -, hsrc'⟩, hv'⟩ := h'
    subst hfr hfr'
    obtain rfl := readSource_unique hX hg hsrc hsrc'
    exact baseWrote_functional hX hg hinj hv hv'

/-- `v` is the value the last write of `cell` left: a write of the cell before which every other
write of the cell is ordered. -/
def LastWrote (L : Launch) (A : List Assumption) (X : Execution) (cell : Cell) (v : Value) :
    Prop :=
  ∃ s, Wrote L A X s cell v ∧ ∀ o, TmemWrite L X o cell → o = s ∨ WriteBefore L X o s

/-- **The last write of a cell left one value.** -/
theorem lastWrote_unique (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hinj : LayoutInjective X)
    {cell : Cell} {v v' : Value} (h : LastWrote L A X cell v) (h' : LastWrote L A X cell v') :
    v = v' := by
  obtain ⟨s, hw, hs⟩ := h
  obtain ⟨s', hw', hs'⟩ := h'
  have heq : s = s' := by
    rcases hs' s hw.tmemWrite with h1 | h1
    · exact h1
    · rcases hs s' hw'.tmemWrite with h2 | h2
      · exact h2.symm
      · exact (writeBefore_asymm hX hg h1 h2).elim
  subst heq
  exact wrote_functional hX hg hinj hw hw'

end
end PTX.TcMma
