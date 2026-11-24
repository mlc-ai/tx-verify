-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Table
public import Lemmas.Tmem.Tmem1Protocol

@[expose] public section

/-! # The Tensor Memory allocation classes from a role table (`cta_group::1`)

A proof skeleton, generic over the kernel, for ERR-TMEM-RESOURCE (`Tmem.Pair.ResourceUnsafe`) and
ERR-TMEM-NOT-RELEASED (`Tmem.Pair.ReleaseUnsafe`) in a kernel whose warp `w` of each CTA
allocates all 512 columns, relinquishes and deallocates (`Lemmas/Tmem/Tmem1Protocol.lean`). The
facts `Tmem.One.Tmem1Facts` asks are per-state facts of a role table that follows every launched
thread (`RoleTable.tmem1Facts`): a resource event of a state is warp `w`'s, in group one, and its
shape is the thread's count of resource events so far (a ledger count, `Frame.count_eq`); a
deallocation frees column 0 (the base word the allocation stored, `Consistent.alloc512_result`);
a lane of warp `w` exits after its three operations. -/

namespace PTX.Frame

open PTX PTX.Flow Tmem.Pair

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C}

/-- **The facts of a `cta_group::1` allocation from a role table** that follows every launched
thread: per state, the resource events' warp, group and shape, a deallocation's column, and the
operations before an exit of warp `w`. -/
theorem RoleTable.tmem1Facts (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    {S : Nat → Prop} (hT : T.ShapeOk S) (hF : T.Followed X S) (hall : ∀ g < L.threads, S g)
    {w : Nat} (hw : (w + 1) * 32 ≤ L.block)
    (hres : ∀ g k d pc grp dst act, S g → stateAt C X g k = some (some d) → T.J g d →
      (C g).inv d → T.Ev g d ⟨pc, .tc (.resource grp dst act)⟩ →
      g % L.block / 32 = w ∧ grp = .one ∧ TmemShape (tmemOps ((X.tr g).take k)) act ∧
        ∀ a n, act = .dealloc a n → a = 0)
    (hexit : ∀ g k d pc, S g → stateAt C X g k = some (some d) → T.J g d → (C g).inv d →
      T.Ev g d ⟨pc, .exit⟩ → g % L.block / 32 = w →
      tmemOps ((X.tr g).take k) = 3) :
    Tmem.One.Tmem1Facts L X w := by
  have res : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request},
      g < L.threads → X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩ →
      g % L.block / 32 = w ∧ grp = .one ∧ TmemShape (tmemOps ((X.tr g).take k)) act ∧
        ∀ a n, act = .dealloc a n → a = 0 := by
    intro g k pc grp dst act hg he
    exact RoleTable.forall_at hC hX hT hF (P := fun e => e = ⟨pc, .tc (.resource grp dst act)⟩)
      (Q := fun i _ => i.1 % L.block / 32 = w ∧ grp = .one ∧
        TmemShape (tmemOps ((X.tr i.1).take i.2)) act ∧ ∀ a n, act = .dealloc a n → a = 0)
      (fun e he f hf => by subst he; cases hf)
      (fun g k d e hg hσ hJ hi hev he' => by
        subst he'
        exact hres g k d pc grp dst act hg hσ hJ hi hev)
      (hall g hg) he rfl
  refine ⟨⟨hw, fun hg he => ?_⟩, fun hg he => ?_, fun hg hgw he => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := res hg he
    exact ⟨h1, h2, h3⟩
  · exact (res hg he).2.2.2 _ _ rfl
  · rename_i g k pc
    exact RoleTable.forall_at hC hX hT hF (P := fun e => e = ⟨pc, .exit⟩)
      (Q := fun i _ => i.1 % L.block / 32 = w → tmemOps ((X.tr i.1).take i.2) = 3)
      (fun e he f hf => by subst he; cases hf)
      (fun g k d e hg hσ hJ hi hev he' => by
        subst he'
        exact hexit g k d pc hg hσ hJ hi hev)
      (hall g hg) he rfl hgw

/-- **ERR-TMEM-RESOURCE and ERR-TMEM-NOT-RELEASED** for a `cta_group::1` allocation, from the
role table's facts. -/
theorem tmem1_safe (hX : Consistent L K A mem0 X) {w : Nat}
    (ht : Tmem.One.Tmem1Facts L X w) :
    ¬ Tmem.Pair.ResourceUnsafe L X ∧ ¬ Tmem.Pair.ReleaseUnsafe L X :=
  ⟨Tmem.One.no_resource_unsafe hX ht, Tmem.One.no_release_unsafe hX ht⟩

end

end PTX.Frame
