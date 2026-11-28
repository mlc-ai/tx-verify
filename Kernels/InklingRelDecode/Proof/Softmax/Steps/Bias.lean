-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.BiasFrame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

theorem Bias.read_step {e L g i v} (b : Bias) (j : Fin 64) (z : Site)
    (dst : Inv e (g % L.block) ⟨b.site j,i,v⟩ → Inv e (g % L.block) ⟨z,i,v⟩)
    (go : ∀ ev, next e L g ⟨b.site j,i,v⟩ ev = some (some ⟨z,i,v⟩))
    (seg : SegU kernel Assumptions.all L g ((b.site j).pc+1)
      (facts e L g ⟨b.site j,i,v⟩ (b.site j).pc) z.pc (facts e L g ⟨z,i,v⟩ z.pc)) :
    (code e L g).StepAtU ⟨b.site j,i,v⟩ := by
  apply step_of_inv
  intro hi
  obtain ⟨a,fetch,load,nc,ext,reg,localOp⟩ := b.load j
  exact Code.guardedLoadU (C := code e L g) (d := ⟨b.site j,i,v⟩) (dn := ⟨z,i,v⟩)
    fetch localOp (b.active j hi) load nc ext reg rfl rfl rfl rfl
    (fun l xs => go ⟨(b.site j).pc,.rd l xs⟩)
    (dst hi) (b.free j) seg

/-- The first 63 loads in each bias stream. Every read payload is admitted. -/
theorem Bias.step_inner {e L g i v} (b : Bias) (j : Fin 63) :
    (code e L g).StepAtU ⟨b.site ⟨j.val,by omega⟩,i,v⟩ := by
  apply b.read_step _ (b.site ⟨j.val+1,by omega⟩) _ _ (b.frame j)
  · intro hi
    cases b with
    | pre =>
      obtain ⟨zero,act⟩ := hi.pre _ rfl
      refine ⟨hi.entry, hi.thread, hi.bound, fun _ => zero, fun _ _ => ⟨zero,act⟩, ?_, ?_, ?_⟩
      · intro j h; cases h
      · intro h; cases h
      · intro _ _ _ h; exact (h _ rfl).elim
    | nxt =>
      have act := hi.nxt _ rfl
      refine ⟨hi.entry, hi.thread, hi.bound, ?_, ?_, fun _ _ => act, ?_, ?_⟩
      · rintro (h|h) <;> cases h
      · intro j h; cases h
      · intro h; cases h
      · intro _ _ _ _
        exact hi.loop (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (fun _ => nofun)
  · intro ev
    cases b <;> simp only [Bias.site,next,dite_eq_left (by omega : j.val+1 < 64)]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
