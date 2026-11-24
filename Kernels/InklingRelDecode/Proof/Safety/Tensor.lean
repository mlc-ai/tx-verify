-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Objects
public import Lemmas.Flow.NotTensorPrefetch

@[expose] public section

/-!
# The tensor-load branches of `Unsafe`

Every tensor copy of the kernel goes through the `kv_desc` map (`Q.kvMap`), which `Pre.mapKvBind`
binds to `mapKv`: bf16 elements, 128-byte swizzle, zero fill. Then:

* **`TensorUnsafe`** (a load writes a byte without a scalar value): a slot's content is the byte
  read or the descriptor's fill, and the zero fill of a bf16 map has a byte. This does not need
  the box inside the map. It needs the copy's map operand to be the `kv_desc` object
  (`KvMapOnly`): the loader's copies are (`EvW.LdShape`), the prologue's are a fact of the
  prologue's registers (a row of "thread-layer gaps").
* **`TensorAllocationUnsafe`** (an out-of-bounds element of a large-class map without backing):
  there is no tensor store and no prefetch, and no load selects an out-of-bounds element when its
  box is inside the cache view (`BoxInBounds`: `Pre.slabInside` and `kvCols` with the origins of
  the copies).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow TensorDescriptor PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every tensor copy names the `kv_desc` map.** -/
def KvMapOnly (Q : Params) (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {s : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ → a = Q.kvMap

/-- **Every tensor copy's box is inside the map.** -/
def BoxInBounds (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {s : TensorCopy.Spec},
    X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ → ¬ TensorHasOob s.descriptor s.origin s.rows

theorem fill_of_heq (n : Nat) (d1 : Descriptor n) (d2 : Descriptor 1) (hn : n = 1)
    (hh : HEq d1 d2) : d1.fill = d2.fill ∧ d1.format = d2.format := by
  subst hn
  cases eq_of_heq hh
  exact ⟨rfl, rfl⟩

/-- **A tensor copy's descriptor fills with zero, over bf16 elements, and the copy lands in shared
memory.** -/
theorem issue_fill (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hm : KvMapOnly Q X) {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) :
    s.descriptor.fill = .zero ∧ s.descriptor.format = .bf16 ∧ s.sharedBase.space = .shared := by
  have hg := Frame.lt_of_get hX he
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, s, rfl⟩ with
    ⟨d, hσ, i, hi, hsite, a', s', hev, h1, h2, h3, h4, h5, h6, desc, hmap, hdesc⟩ |
    ⟨d, P, hσ, hld⟩
  · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, h_a, h_s⟩ := hev
    subst h_a
    subst h_s
    have hmk := hm he
    subst hmk
    have hb := hmap.symm.trans hpre.mapKvBind
    obtain ⟨hout, hh⟩ := Sigma.mk.inj_iff.mp (Option.some.inj hb)
    have hh' : HEq s.descriptor (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass) := by
      rw [hdesc]; exact hh
    obtain ⟨hfl, hfm⟩ := fill_of_heq s.outer s.descriptor _ hout hh'
    exact ⟨hfl, hfm, by rw [h4]⟩
  · cases hs : d.site <;> simp [EvW.LdShape, hs] at hld
    all_goals rcases hld with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, -, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-- **No tensor load writes a byte without a scalar value.** -/
theorem no_tensorUnsafe (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hm : KvMapOnly Q X) : ¬ TensorUnsafe X := by
  rintro ⟨i, o, slot, content, hobs, hw, hbyte⟩
  obtain ⟨⟨address, pc, he⟩, hok, -, -⟩ := hX.tensor i o hobs
  obtain ⟨hfill, hfmt, -⟩ := issue_fill hpre hX hf hm he
  have hwr := hok.writes slot content hw
  unfold TensorCopy.source at hwr
  cases hg : o.spec.globalAddress slot with
  | some address' =>
    simp only [hg] at hwr
    obtain ⟨byte, -, rfl⟩ := hwr
    simp [TensorCopy.Content.byte] at hbyte
  | none =>
    simp only [hg] at hwr
    rw [hfill] at hwr
    have hz : (TensorCopy.zeroValue o.spec.descriptor.format).isSome = true := by
      rw [hfmt]; rfl
    simp only [hwr, TensorCopy.Content.byte, Option.map_eq_none_iff] at hbyte
    rw [hbyte] at hz
    cases hz

/-- **The kernel has no tensor prefetch.** -/
theorem kernel_noTensorPrefetch :
    kernel.code.all (fun ins => !tensorPrefetchOp ins.op) = true := by decide +kernel

theorem no_tensorPrefetch (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc a : Nat} {s : TensorPrefetch.Spec},
      X.get i ≠ some ⟨pc, .tensorPrefetch a s⟩ :=
  fun he => no_kind_of_code hX tensorPrefetchOp (fun k => ∃ a s, k = .tensorPrefetch a s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_tensorPrefetch_op hf hk)
    kernel_noTensorPrefetch he ⟨_, _, rfl⟩

/-- **No tensor operation is an out-of-bounds access to a large allocation without backing.** -/
theorem no_tensorAllocUnsafe (hX : Consistent L kernel asms mem0 X) (hb : BoxInBounds X) :
    ¬ TensorAllocationUnsafe L mem0 X := by
  rintro ⟨i, ⟨address, s, ⟨pc, he⟩, -, hoob, -⟩ | ⟨address, s, ⟨pc, he⟩, -⟩ |
    ⟨address, s, ⟨pc, he⟩, -⟩⟩
  · obtain ⟨g, k⟩ := i
    exact hb he hoob
  · exact no_tensorStore hX he
  · exact no_tensorPrefetch hX he

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
