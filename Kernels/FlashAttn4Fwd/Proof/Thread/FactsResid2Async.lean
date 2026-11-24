-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressAsync
public import Lemmas.Flow.StoreValid
public import Lemmas.Flow.TensorLoadFacts
public import Lemmas.Tensor.TensorMulticast

@[expose] public section

/-! # The tensor loads' routes and the tensor stores' specifications

`ProgressAsyncFacts.copy_route` and `ProgressAsyncFacts.store_valid`. A unicast tensor load
through a cluster address, with or without a cache policy, issues its copy only when the copy is
routed from the issuing CTA, and the map it reads has a valid descriptor
(`fires_cpTensor_route_policy`). Every tensor load of the kernel is such a tile-mode load
(`kernel_copy_form`), so every copy is routed and has a valid descriptor. A tile-mode tensor
store fired by its instruction has a valid specification (`Flow.fires_cpTensorStore_form`), and
every tensor store of the kernel is in tile mode (`kernel_store_form`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A tensor load's route, under any cache policy.** A unicast tensor load through a cluster
address issues a copy routed from the issuing CTA. -/
theorem fires_cpTensor_route_policy {A : List Assumption} {g : Nat} {t : TState}
    {o : Option TState} {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor true grp dst off map cs mb moff none lm pol)) e o)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    TensorCopy.RoutingOk L (g / L.block) s := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor true grp dst off map cs mb moff none lm pol)) e
      o := hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf'
  rcases hp : cachePolicyRead L g t pol with f | ⟨⟩ <;> rw [hp] at hf'
  · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk
  · rcases hc : tensorLoadCopy L g t true grp dst off map cs mb moff lm with f | ⟨a', s'⟩ <;>
      rw [hc] at hf'
    · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk
    · dsimp only at hf'
      split_ifs at hf' with hr
      · simp only [Fires] at hf'
        rw [hf'.1] at hk
        cases hk
        exact hr
      · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk

/-- A tile-mode unicast tensor load through a cluster address. -/
def copyForm : Op → Bool
  | .cpTensor ca _ _ _ _ _ _ _ mc mode _ => ca && mc.isNone && mode == .tile
  | _ => false

/-- Every tensor load of the kernel is a tile-mode unicast load through a cluster address. -/
theorem kernel_copy_form :
    OpPcsFast kernel.code (fun op => tensorOp op && !copyForm op) [] = true := by
  decide +kernel

/-- Every tensor store of the kernel is in tile mode. -/
theorem kernel_store_form : OpPcsFast kernel.code
    (fun op => match op with | .cpTensorStore _ _ _ _ _ mode _ => mode != .tile | _ => false)
    [] = true := by
  decide +kernel

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`ProgressAsyncFacts.copy_route`**: a tensor load's copy is routed from the issuing CTA and
its descriptor is valid. -/
theorem ProgressAsyncFacts_copy_route : ∀ {i : EvId} {pc a : Nat} {s : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a s⟩ →
      TensorCopy.RoutingOk L (i.1 / L.block) s ∧ TensorDescriptor.Valid s.descriptor := by
  rintro ⟨g, k⟩ pc a s he
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => Cross.trueJ_run L g) he
      (fun _ _ h => by cases h)
  have hk : (⟨pc, .tensorIssue a s⟩ : Event).kind = .tensorIssue a s := rfl
  have htop := Loader.tensorOp_of hf hk
  have hform : copyForm ins.op = true := by
    by_contra hne
    exact absurd (OpPcsFast.mem kernel_copy_form hc (by simp [htop, hne])) (by simp)
  generalize ins.op = op at hf hform
  cases op <;> simp only [copyForm, Bool.false_eq_true] at hform
  rename_i ca grp dst off map cs mb moff mc mode pol
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hform
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hform
  refine ⟨fires_cpTensor_route_policy hf hk, ?_⟩
  obtain ⟨-, -, d', hd, hv, hdesc, -⟩ := tensorLoadCopy_ok (fires_cpTensor_copy hf hk)
  rw [hdesc]
  exact hv

/-- **`ProgressAsyncFacts.store_valid`**: a tensor store's specification is valid. -/
theorem ProgressAsyncFacts_store_valid : ∀ {i : EvId} {pc a : Nat} {s : TensorStore.Spec},
    X.get i = some ⟨pc, .tensorStore a s⟩ → TensorStore.Valid (i.1 / L.block) s := by
  rintro ⟨g, k⟩ pc a s he
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => Cross.trueJ_run L g) he
      (fun _ _ h => by cases h)
  have hk : (⟨pc, .tensorStore a s⟩ : Event).kind = .tensorStore a s := rfl
  have hop := fires_tensorStore_op hf hk
  generalize hins : ins.op = op at hf hop
  cases op <;> simp only [tensorStoreOp, Bool.false_eq_true] at hop
  rename_i map cs src off pol mode red
  cases mode
  · exact (fires_cpTensorStore_form hf a s hk).1
  · exact absurd (OpPcsFast.mem kernel_store_form hc (by rw [hins]; rfl)) (by simp)

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
