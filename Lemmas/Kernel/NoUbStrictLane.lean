-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.NoUbFirstStop
public import Lemmas.Kernel.StrictSite
public import Lemmas.Kernel.Safety.TableU
public import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # No undefined behaviour in a lane, at its first undefined-behaviour event

A proof skeleton, generic over the kernel. An undefined-behaviour event ends its thread
(`ub_last`), so at the first one every earlier event of the lane is an ordinary event. Then:

* if the machine is alive before it, the step into that state was strict (`strict`, for the
  actual event, under the prefix without undefined behaviour), so the concrete state is strictly
  good (`strict_site`) and the site's template is not undefined behaviour (`safe`);
* if the machine is dead before it, the machine lost the lane at an earlier event with no
  undefined behaviour before it, and the lane's last event is an exit (`live`), which no event
  follows. -/

namespace PTX.Frame

open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : ∀ g, Code K A L g} {J : ∀ g, (C g).D → Prop} {X : Execution}

/-- **A lane has no undefined-behaviour event**, from the strict steps along its prefixes, the
templates of the sites of strictly good states, and the machine's dying only at the exit. -/
theorem noUb_strict_lane (hC : ∀ g < L.threads, (C g).SoundU)
    (hX : Consistent L K A mem0 X) {g : Nat} (hF : ∀ k, FollowedAt C J X g k)
    {R : (C g).D → Prop} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (strict : ∀ j dj ej, R dj → X.get (g, j) = some ej → stateAt C X g j = some (some dj) →
      NoUbBefore X g (j + 1) → (C g).StepFor dj ej)
    (safe : ∀ σ t ins, stateAt C X g k = some (some σ) → J g σ → e.pc = (C g).pc σ →
      (C g).Good (some σ) t → K.code[(C g).pc σ]? = some ins →
      ∀ f, eventTmpl A L g t ins.op ≠ .ub f)
    (live : ∀ i d v, R d → X.get (g, i) = some v → stateAt C X g i = some (some d) → J g d →
      NoUbBefore X g (i + 1) → (C g).next d v = none → v.kind = .exit)
    (hR : ∀ j d, j < k → stateAt C X g j = some (some d) → R d) (f : Fault) : e.kind ≠ .ub f := by
  intro hk
  have nu := noUbBefore_of_get hX he
  have hg := lt_of_get hX he
  cases hs : stateAt C X g k with
  | some o =>
    cases o with
    | some σ =>
      have hprev : ∀ j dj ej, j + 1 = k → (X.tr g)[j]? = some ej →
          stateAt C X g j = some (some dj) → (C g).next dj ej = some (some σ) →
          (C g).StepFor dj ej := by
        intro j dj ej hj hej hdj _
        subst hj
        exact strict j dj ej (hR j dj (by omega) hdj) hej hdj nu
      obtain ⟨t, o', ins, hgood, hc, hfire⟩ := strict_site hC hX he hs hprev
      have hu := fires_ub hfire hk
      exact safe σ t ins hs ((hF k).2 σ hs) (EventFrame.fires_source_pc hfire) hgood hc f hu
    | none => exact (hF k).1 hs
  | none =>
    obtain ⟨i, hik, d, v, hi, hd, hn, prefixLive⟩ := first_stop_event (C := C) (g := g)
      (k := k) (.inl hs)
    have hn' : (C g).next d v = none :=
      next_none_of_stop hi hd hn (fun h => (hF (i + 1)).1 h)
    have hx := live i d v (hR i d hik hd) hi hd ((hF i).2 d hd) (fun u hu => nu u (by omega)) hn'
    obtain ⟨r, hr⟩ := hX.thr g hg
    obtain ⟨pc, kd⟩ := v
    change kd = .exit at hx
    subst hx
    have hl := Flow.Run.end_last hr hi (.inr rfl)
    have hk' : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    omega

end PTX.Frame
