-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed
public import Lemmas.Kernel.NoUbFirstStop

@[expose] public section
namespace PTX.Frame
open PTX.Flow
variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : ∀ g, Code K A L g} {J : ∀ g, (C g).D → Prop} {X : Execution}

/-- An invariant that excludes UB at each followed site and permits death only at exit
excludes UB throughout the thread. -/
theorem noUb_of_followed_sites
    (hX : Consistent L K A mem0 X)
    {g : Nat} (hF : ∀ k, FollowedAt C J X g k)
    (safe : ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      ∀ f, e.kind ≠ .ub f)
    (live : ∀ k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      (∀ f, e.kind ≠ .ub f) → (C g).next d e = none → e.kind = .exit)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  refine noUb_of_first_stop (C := C) hX
    (fun i d v hi hd => safe i d v hi hd ((hF i).2 d hd)) ?_ he f
  intro i d v hi hd _ hn
  have inv := (hF i).2 d hd
  exact live i d v hi hd inv (safe i d v hi hd inv)
    (next_none_of_stop hi hd hn (hF (i+1)).1)

end PTX.Frame
