-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.TensorStore.TensorReduce
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Tensor.TensorCompleteConsistentRead
public import Assumption.IdealReal
public import Mathlib.Tactic

/-!
# Tensor reduction values and element-wise atomicity (DEP-REDUCTION-VALUES)

`cp.reduce.async.bulk.tensor` on a `.u32` map, one element at global address 4096 (W0 = 10).

* Values: an element is written as `op(old, src)`, integer operations exactly (add wraps, signed
  min, `atom`'s inc and dec); floating add only through a scoped
  `Assumption.idealReal`.
* One `.add` of 3: the written element is `old + 3`.
* Two concurrent `.add`s of 3 and 4: the execution in which the second reads the first's write
  (final value 17 = 10 + 3 + 4) satisfies the rule; the lost update, in which both read W0
  (final value 13 or 14), does not.
* No rule is unsafe: an f32 reduction with no floating rule (no assumption) has no value and makes
  the execution `TensorStoreUnsafe` (`ReduceNoRule`); the u32 reductions above have values, so
  the chain has no unsafe reduction.
* A reduction and an unordered plain `st.u8` of a byte of the element are a `Race`.
-/

namespace PTX.Tests.TensorReduceAtomic
open TensorStore
noncomputable section

private def u32 (v : Nat) : Value := .bits 32 (BitVec.ofNat 64 v)
private def bytesOf (v : Value) (n : Nat) : List (Option Byte) :=
  (List.range n).map fun k => some (v.byteAt k)

private theorem rebuild_whole (v : Value) (n : Nat) (hn : v.bytes = n + 1) (h0 : v.byteAt 0 = (v,
    0)) :
    rebuild 3 (bytesOf v (n + 1)) = .ok v := by
  have hb : bytesOf v (n + 1) = v.toBytes.map some := by simp [bytesOf, Value.toBytes, hn]
  have hcons : bytesOf v (n + 1) = some (v, 0) :: (bytesOf v (n + 1)).tail := by
    simp [bytesOf, List.range_succ_eq_map, h0]
  rw [hcons, rebuild, ← hcons, ite_eq_left ⟨by simp [bytesOf, hn], hb⟩]
  rfl

private theorem rebuild_u32 (v : Nat) : rebuild 3 (bytesOf (u32 v) 4) = .ok (u32 v) :=
  rebuild_whole _ 3 rfl rfl

/-! ## Operations -/

example : reduceValue [] .add .u32 (bytesOf (u32 10) 4) (bytesOf (u32 3) 4) = .ok (u32 13) := by
  simp only [reduceValue, rebuild_u32]; rfl
-- Add wraps at the element width.
example : reduceValue [] .add .u32 (bytesOf (u32 0xFFFFFFFF) 4) (bytesOf (u32 2) 4) =
    .ok (u32 1) := by
  simp only [reduceValue, rebuild_u32]; rfl
-- min compares as signed for `.s32` (-1 < 1) and as unsigned for `.u32`.
example : reduceValue [] .min .s32 (bytesOf (u32 0xFFFFFFFF) 4) (bytesOf (u32 1) 4) =
    .ok (u32 0xFFFFFFFF) := by
  simp only [reduceValue, rebuild_u32]; rfl
example : reduceValue [] .min .u32 (bytesOf (u32 0xFFFFFFFF) 4) (bytesOf (u32 1) 4) =
    .ok (u32 1) := by
  simp only [reduceValue, rebuild_u32]; rfl
-- inc and dec are `atom`'s: `(r >= s) ? 0 : r+1` and `(r==0 || r > s) ? s : r-1`.
example : reduceValue [] .inc .u32 (bytesOf (u32 5) 4) (bytesOf (u32 5) 4) = .ok (u32 0) := by
  simp only [reduceValue, rebuild_u32]; rfl
example : reduceValue [] .inc .u32 (bytesOf (u32 4) 4) (bytesOf (u32 5) 4) = .ok (u32 5) := by
  simp only [reduceValue, rebuild_u32]; rfl
example : reduceValue [] .dec .u32 (bytesOf (u32 0) 4) (bytesOf (u32 7) 4) = .ok (u32 7) := by
  simp only [reduceValue, rebuild_u32]; rfl
example : reduceValue [] .dec .u32 (bytesOf (u32 9) 4) (bytesOf (u32 7) 4) = .ok (u32 7) := by
  simp only [reduceValue, rebuild_u32]; rfl
example : reduceValue [] .dec .u32 (bytesOf (u32 3) 4) (bytesOf (u32 7) 4) = .ok (u32 2) := by
  simp only [reduceValue, rebuild_u32]; rfl
example : reduceValue [] .xor .u32 (bytesOf (u32 6) 4) (bytesOf (u32 3) 4) = .ok (u32 5) := by
  simp only [reduceValue, rebuild_u32]; rfl
-- Floating reductions have no Core rule; a scoped `idealReal` supplies the real sum.
private def idealAddF32 : Assumption :=
  Assumption.idealReal "test-ideal-add-f32" { rmw := [(.add, .float .f32)] } "test"

private theorem rebuild_f32 (x : ℝ) : rebuild 3 (bytesOf (.float .f32 x) 4) = .ok (.float .f32 x) :=
  rebuild_whole _ 3 rfl rfl
example : reduceValue [] .add .f32 (bytesOf (.float .f32 1) 4) (bytesOf (.float .f32 2) 4) =
    .error .noRule := by
  simp only [reduceValue, rebuild_f32]; rfl
example : reduceValue [idealAddF32] .add .f32 (bytesOf (.float .f32 1) 4)
    (bytesOf (.float .f32 2) 4) = .ok (.float .f32 3) := by
  simp only [reduceValue, rebuild_f32]
  change (Assumption.idealRmw .add (.float .f32) (.float .f32 1) (.float .f32 2)).getD
    (.error .noRule) = _
  simp only [Assumption.idealRmw, valFloat, Option.getD_some]
  norm_num
  rfl
-- A reduction outside the assumption's scope gets no rule from it.
example (old src : Value) : idealAddF32.rmwRule .max (.float .f32) old src = none := rfl

/-! ## One element, two reductions -/

private def map : TensorDescriptor.Descriptor 1 :=
  ⟨.u32, 4096, ![64, 32], ![256], ⟨![16, 8], ![1, 1]⟩, .none, .zero, .small⟩
private def spec : Spec := ⟨⟨1, map, ![0, 0], ⟨.shared, 0, 0⟩, none⟩, some .add⟩
private def fp : Acc := { loc := ⟨.global, 0, 4096⟩, size := 4 }
private theorem writeLoc00 : writeLoc spec 0 0 0 = some fp.loc := rfl
private theorem slotAt00 (k : Fin 4) :
    TensorTransfer.slotAt map 0 0 k.val = some (⟨0, by decide⟩, ⟨0, by decide⟩, k) := by
  fin_cases k <;> rfl

/-- Element `(0, 0)` holds the bytes of `v`; no other element has a byte. -/
private def elem (v : Nat) (s : TensorTransfer.Slot map) : Option Byte :=
  if s.1.val = 0 ∧ s.2.1.val = 0 then some ((u32 v).byteAt s.2.2.val) else none
/-- A performed `.add` of `src` that read `old` and wrote `new`. -/
private def obs (src old new : Nat) : Observation :=
  ⟨spec, { read := elem src, old := elem old, write := elem new }⟩

private theorem view_elem (v k : Nat) (hk : k < 4) :
    (TensorTransfer.slotAt map 0 0 k).bind (elem v) = some ((u32 v).byteAt k) := by
  have h := slotAt00 ⟨k, hk⟩
  simp only at h
  rw [h]
  change elem v (⟨0, by decide⟩, ⟨0, by decide⟩, ⟨k, hk⟩) = _
  exact ite_eq_left ⟨rfl, rfl⟩

private theorem obs_spec (src old new : Nat) : (obs src old new).spec = spec := rfl

private theorem elem_bytes (src old new : Nat) :
    elementBytes oldByte (obs src old new) 0 0 = bytesOf (u32 old) 4 ∧
      elementBytes readByte (obs src old new) 0 0 = bytesOf (u32 src) 4 := by
  constructor <;>
  · unfold elementBytes bytesOf
    rw [obs_spec]
    refine List.map_congr_left fun k hk => ?_
    exact view_elem _ k (by simpa [spec, map, TensorDescriptor.Format.bytes] using hk)

private theorem written {src old new x y : Nat} (h : (writeByte (obs src old new) x y 0).isSome) :
    x = 0 ∧ y = 0 := by
  change ((TensorTransfer.slotAt map x y 0).bind (elem new)).isSome at h
  cases hs : TensorTransfer.slotAt map x y 0 with
  | none => simp [hs] at h
  | some s =>
    have hc := TensorCopy.slotAt_coordinates hs
    simp only [hs, Option.bind_some, elem] at h
    split_ifs at h with he
    · exact ⟨hc.1 ▸ he.1, hc.2.1 ▸ he.2⟩
    · cases h

/-- With W0 = 10, a single `.add` of 3 writes 13: the written element is `old + src`. -/
theorem single_add {A : List Assumption} {X : Execution} {i : EvId} {w : Nat}
    (h : ReduceValues A X) (ho : X.tensorStores i = some (obs 3 10 w)) :
    ∀ k < 4, writeByte (obs 3 10 w) 0 0 k = some ((u32 13).byteAt k) := by
  have hv : reduceValue A .add .u32 (bytesOf (u32 10) 4) (bytesOf (u32 3) 4) = .ok (u32 13) := by
    simp only [reduceValue, rebuild_u32]; rfl
  have hw : (writeByte (obs 3 10 w) 0 0 0).isSome := by
    change ((TensorTransfer.slotAt map 0 0 0).bind (elem w)).isSome
    rw [view_elem w 0 (by decide)]; rfl
  have hk := h i _ .add 0 0 (u32 13) ho rfl hw (by rw [(elem_bytes 3 10 w).1,
                                                       (elem_bytes 3 10 w).2]; exact hv)
  exact hk

private def p : EvId := (0, 0)
private def q : EvId := (1, 0)
private def L : Launch := { grid := 1, block := 64, params := fun _ => none }
private def issue : List Event := [⟨0, .tensorStore 1024 spec⟩]

/-- The second reduction read the first one's write: 10 + 3 = 13, then 13 + 4 = 17. -/
private def rfChain : AsyncCopy.Ref → Nat → Option AsyncCopy.Ref
  | .async (1, 0) (.old (.store 0 0 k)), 0 => some (.async (0, 0) (.write (.store 0 0 k)))
  | _, _ => none
private def chain : Execution where
  tr g := if g = 0 ∨ g = 1 then issue else []
  rf := rfChain
  tensorStores i := if i = p then some (obs 3 10 13) else if i = q then some (obs 4 13 17) else none

/-- Both reductions read W0: the lost update (final value 13 or 14 instead of 17). -/
private def lost : Execution where
  tr g := if g = 0 ∨ g = 1 then issue else []
  rf _ _ := none
  tensorStores i := if i = p then some (obs 3 10 13) else if i = q then some (obs 4 10 14) else none

private theorem stores_cases {X : Execution} {a b c d : Nat}
    (hX : X.tensorStores = fun i => if i = p then some (obs 3 a b) else if i = q then
      some (obs 4 c d) else none) {i : EvId} {o : Observation} (ho : X.tensorStores i = some o) :
    (i = p ∧ o = obs 3 a b) ∨ (i = q ∧ o = obs 4 c d) := by
  rw [hX] at ho
  by_cases hp : i = p
  · subst hp; simp at ho; exact .inl ⟨rfl, ho.symm⟩
  · by_cases hq : i = q
    · subst hq; simp [show q ≠ p by decide] at ho; exact .inr ⟨rfl, ho.symm⟩
    · simp [hp, hq] at ho

private theorem reduced_cases {X : Execution} {a b c d : Nat}
    (hX : X.tensorStores = fun i => if i = p then some (obs 3 a b) else if i = q then
      some (obs 4 c d) else none) {e : EvId × Nat × Nat} {f : Acc}
    (h : Reduced X e.1 e.2.1 e.2.2 f) : (e = (p, 0, 0) ∨ e = (q, 0, 0)) ∧ f = fp := by
  obtain ⟨o, red, loc, ho, -, hl, rfl, hw⟩ := h
  obtain ⟨i, x, y⟩ := e
  rcases stores_cases hX ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := written hw
    rw [obs_spec, writeLoc00] at hl
    cases hl
    exact ⟨.inl rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := written hw
    rw [obs_spec, writeLoc00] at hl
    cases hl
    exact ⟨.inr rfl, rfl⟩

private theorem add_u32 (a s r : Nat) (h : reduceValue [] .add .u32 (bytesOf (u32 a) 4)
    (bytesOf (u32 s) 4) = .ok (u32 r)) {o : Observation} (ho : o =
      obs s a r) {v : Value} {x y : Nat}
    (hw : (writeByte o x y 0).isSome)
    (hv : reduceValue [] .add o.spec.descriptor.format (elementBytes oldByte o x y)
      (elementBytes readByte o x y) = .ok v) {k : Nat} (hk : k < o.spec.descriptor.format.bytes) :
    writeByte o x y k = some (v.byteAt k) := by
  subst ho
  obtain ⟨rfl, rfl⟩ := written hw
  rw [(elem_bytes _ _ _).1, (elem_bytes _ _ _).2, obs_spec, show spec.descriptor.format =
    .u32 from rfl,
    h] at hv
  cases hv
  have hk4 : k < 4 := by rw [obs_spec] at hk; exact hk
  exact view_elem r k hk4

private theorem values_of {X : Execution} {a b c d : Nat}
    (hX : X.tensorStores = fun i => if i = p then some (obs 3 a b) else if i = q then
      some (obs 4 c d) else none)
    (hab : reduceValue [] .add .u32 (bytesOf (u32 a) 4) (bytesOf (u32 3) 4) = .ok (u32 b))
    (hcd : reduceValue [] .add .u32 (bytesOf (u32 c) 4) (bytesOf (u32 4) 4) = .ok (u32 d)) :
    ReduceValues [] X := by
  intro i o red x y v ho hr hw hv k hk
  rcases stores_cases hX ho with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · cases hr; exact add_u32 a 3 b hab rfl hw hv hk
  · cases hr; exact add_u32 c 4 d hcd rfl hw hv hk

/-- **Allowed**: the second `.add` reads the first one's write; the element ends at 17. The
written values follow the rule, there is no linear reduction, and the two elements read their old
bytes uniquely and without a cycle (the conclusions MEM-ATOMICITY gives, `Consistent.reduceUnique`,
`Consistent.reduceAcyclic`). -/
theorem chain_ok : ReduceOk [] chain ∧ ReduceUnique chain ∧ ReduceAcyclic chain := by
  refine ⟨⟨values_of rfl (by simp only [reduceValue, rebuild_u32]; rfl)
    (by simp only [reduceValue, rebuild_u32]; rfl), copyReduceValues_of_none ?_⟩, ?_, ?_⟩
  · rintro i s ⟨pc, h⟩
    simp only [Execution.get, chain] at h
    split_ifs at h <;> simp [issue] at h
    all_goals (rcases i with ⟨g, k⟩; cases k <;> simp_all)
  · intro f e e' k he he' hne hk
    obtain ⟨hc, rfl⟩ := reduced_cases rfl he
    obtain ⟨hc', -⟩ := reduced_cases rfl he'
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · exact (hne rfl).elim
    · simp [chain, rfChain, p, q]
    · simp [chain, rfChain, p, q]
    · exact (hne rfl).elim
  · intro f e hc
    -- every edge ends at the second reduction, whose write nobody reads
    have hend : ∀ a b, ReduceReads chain f a b → b = (q, 0, 0) ∧ a = (p, 0, 0) := by
      rintro a b ⟨ha, hb, k, k', -, hk⟩
      obtain ⟨hca, -⟩ := reduced_cases rfl ha
      obtain ⟨hcb, -⟩ := reduced_cases rfl hb
      rcases hcb with rfl | rfl
      · simp [chain, rfChain, p] at hk
      · rcases hca with rfl | rfl
        · exact ⟨rfl, rfl⟩
        · simp [chain, rfChain, q] at hk
    obtain ⟨c, hec, -⟩ := Relation.TransGen.head'_iff.mp hc
    obtain ⟨c', -, hce⟩ := Relation.TransGen.tail'_iff.mp hc
    have h1 := (hend _ _ hec).2
    have h2 := (hend _ _ hce).1
    rw [h1] at h2
    simp [p, q] at h2

/-- **Forbidden**: both `.add`s read W0, losing one update. -/
theorem lost_update : ¬ ReduceUnique lost := by
  intro h
  exact h fp (p, 0, 0) (q, 0, 0) 0 ⟨_, .add, _, rfl, rfl, rfl, rfl, rfl⟩
    ⟨_, .add, _, rfl, rfl, rfl, rfl, rfl⟩ (by simp [p, q]) (by decide) rfl

/-- The lost update is no possible execution of any kernel (MEM-ATOMICITY). -/
theorem lost_update_inconsistent {K : Kernel} {A : List Assumption} {mem0 : Mem0} :
    ¬ Consistent L K A mem0 lost :=
  fun h => lost_update h.reduceUnique

/-! ## A reduction and an unordered plain store of one of its bytes race

The reduction's read of the old byte (`.old`) and the plain store conflict and are unordered. The
reduction's write is not yet performed here, so it has no value to compare with the store's
(ERR-DATA-RACE `SameValueWrites`); the race is the read's. -/

private def byte : Byte := (u32 0).byteAt 0
private def dst : Acc := { loc := fp.loc, size := 1 }
private def racy : Execution where
  tr g := if g = 0 then issue else if g = 1 then [⟨0, .wr dst [byte]⟩] else []
  rf _ _ := none

/-- The issue of the reduction is no copy, so it is not performed in the generic proxy. -/
private theorem racy_not_generic : ¬ GenericCopy racy p := by
  rintro ⟨s, ⟨pc, h⟩, -⟩
  simp [Execution.get, racy, issue, p] at h

theorem reduce_store_race : Race L racy := by
  refine ⟨.async p (.old (.store 0 0 0)), .thread (1, 0), dst, dst, fp.loc,
    ⟨by simp, false, true, ⟨rfl, spec, 1024, ⟨0, rfl⟩, rfl, rfl, rfl⟩,
      .inr (.inl ⟨[byte], ⟨0, rfl⟩, rfl⟩), .inr rfl, fp.loc, ?_, ?_⟩, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_,
    fun ⟨⟨h, _⟩, _⟩ => nomatch h⟩
  all_goals try simp [Acc.Covers, Loc.InRange, dst]
  · rintro ⟨-, hp, -⟩
    exact racy_not_generic (hp.mpr trivial)
  · -- No wait observes the reduction: its read completion is absent and it notifies nothing.
    rw [ByteCausality.direct_iff_of_global rfl]
    rintro ⟨-, w, ⟨k, -, -, hall⟩ | ⟨ws, ⟨n, m, hN, -⟩, -⟩, -⟩
    · have hr : AsyncCopy.Part.readsDone ∈ GroupWaitStages racy p k := by
        rcases k with ⟨_ | _ | _⟩ | _ <;> simp [GroupWaitStages, Execution.get, racy, issue, p]
      obtain ⟨o, ho, -⟩ := hall _ hr
      cases ho
    · exact hN
  · -- No async proxy fence and no generic copy order the store before the reduction.
    rw [ByteCausality.direct_iff_of_global rfl]
    rintro ⟨-, ⟨fence, sp, scope, ⟨pc, hf⟩, -, -, -, -, -⟩ | ⟨hg, -⟩⟩
    · rcases fence with ⟨g, j⟩
      simp only [Execution.get, racy, issue] at hf
      split_ifs at hf <;> (rcases j with _ | _ | j <;> simp at hf)
    · exact racy_not_generic hg

/-! ## No arithmetic rule is unsafe, a rule gives a value -/

private def mapF : TensorDescriptor.Descriptor 1 := { map with format := .f32 }
private def specF : Spec := ⟨⟨1, mapF, ![0, 0], ⟨.shared, 0, 0⟩, none⟩, some .add⟩
private def obsF : Observation := ⟨specF, { read := elem 3, old := elem 10, write := elem 13 }⟩

/-- Without a floating rule an f32 reduction element has no value, whatever its bytes. -/
private theorem no_value_f32 (old src : List (Option Byte)) (v : Value) :
    reduceValue [] .add .f32 old src ≠ .ok v := by
  intro h
  simp only [reduceValue] at h
  cases ha : rebuild 3 old <;> cases hb : rebuild 3 src <;>
    simp [ha, hb, bind, Except.bind, rmwValue, TensorDescriptor.Format.dtype] at h

private def noRuleX : Execution where
  tr g := if g = 0 then [⟨0, .tensorStore 1024 specF⟩] else []
  rf _ _ := none
  tensorStores i := if i = p then some obsF else none

/-- **Unsafe**: a performed f32 reduction with no floating rule. -/
theorem noRule_unsafe : TensorStoreUnsafe [] noRuleX := by
  refine .inl ⟨p, obsF, .add, 0, 0, by simp [noRuleX], rfl, ?_, fun v => ?_⟩
  · change ((TensorTransfer.slotAt mapF 0 0 0).bind (elem 13)).isSome
    change ((TensorTransfer.slotAt map 0 0 0).bind (elem 13)).isSome
    rw [view_elem 13 0 (by decide)]; rfl
  · exact no_value_f32 _ _ v

/-- **Safe**: the u32 reductions of `chain` all have a value. -/
theorem chain_has_rule {A : List Assumption} : ¬ ReduceNoRule A chain := by
  rintro ⟨i, o, red, x, y, ho, hr, hw, hn⟩
  rcases stores_cases (X := chain) rfl ho with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨rfl, rfl⟩ := written hw
    cases hr
    exact hn (u32 13) (by
      rw [(elem_bytes 3 10 13).1, (elem_bytes 3 10 13).2, obs_spec,
        show spec.descriptor.format = .u32 from rfl]
      simp only [reduceValue, rebuild_u32]; rfl)
  · obtain ⟨rfl, rfl⟩ := written hw
    cases hr
    exact hn (u32 17) (by
      rw [(elem_bytes 4 13 17).1, (elem_bytes 4 13 17).2, obs_spec,
        show spec.descriptor.format = .u32 from rfl]
      simp only [reduceValue, rebuild_u32]; rfl)

end
end PTX.Tests.TensorReduceAtomic
