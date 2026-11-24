-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.TensorStore.TensorStoreThread
public import Lemmas.MBarrier.MBarrierAddress

@[expose] public section

/-! Successful tiled output specifications satisfy the actual store validity rule. -/
namespace PTX
namespace TensorStoreValidity
noncomputable section
variable {L : Launch} {g : Nat} {t : TState}

private theorem readSharedAddress_space {w : Nat} {generic cluster : Bool} {a : Opnd} {l : Loc}
    (h : readSharedAddress L g t w generic cluster a = .ok l) : l.space = .shared := by
  unfold readSharedAddress at h
  repeat' first
    | (simp only [bind, Except.bind, pure, Except.pure] at h; split at h)
    | split at h
  all_goals cases h
  all_goals rfl

private theorem sharedEffAddr_space {cluster : Bool} {base : Nat} {off : Int} {l : Loc}
    (h : sharedEffAddr L g t cluster base off = .ok l) : l.space = .shared := by
  unfold sharedEffAddr at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · rename_i loc hl
        cases h
        exact readSharedAddress_space (l := loc) hl
    · split at h
      · cases h
      · cases h; rfl

 theorem tile_valid {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int}
    {policy : Option Opnd} {reduce : Option AtomOp} {address : Nat}
    {s : TensorStore.Spec}
    (h : tensorStoreSpec L g t map cs src off policy .tile reduce=.ok (address,s)) :
    TensorStore.Valid (g/L.block) s := by
  unfold tensorStoreSpec at h
  simp only [bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
  rcases hm : tensorMap L g t map cs .tile with f | ⟨a',outer,d⟩ <;> rw [hm] at h
  · cases h
  obtain ⟨_,_,hv,_⟩ := tensorMap_ok hm
  dsimp only at h
  repeat' (split at h <;> (try (cases h; done)))
  all_goals
    cases h
    refine ⟨hv,?_,?_,?_,?_,?_⟩
    · assumption
    · intro ys he
      cases he
    · apply sharedEffAddr_space
      assumption
    · apply sharedEffAddr_owner
      assumption
    · assumption

end
end TensorStoreValidity
end PTX
