-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # A ready `bar.sync` has every participant's arrival

`Sources.passed_released` and `Sources.member_arrival` (`Lemmas/Protocol/NamedBarSources.lean`)
read the release of a barrier generation off a `bar.sync` that its thread has *passed*: the
thread has a later event, so the arrival has returned and DEP-ORDER fills its needs. A progress
argument meets the same arrival one step earlier: it is the LAST event of its thread, and the
thread is released, that is, the arrival is ready (`Ready`, every need filled), though not yet
returned. The release condition is one of the needs of a `bar.sync` (`ctaBarNeeds`), so
readiness gives the same conclusions:

* `ctaBarDone_of_readyAt`: a ready `bar.sync` has its generation completed;
* `Sources.ready_released`: the generation of its ordinal is released;
* `Sources.ready_member_arrival`: every participant lane of its CTA that never exits has an
  arrival of that ordinal.

Use: a thread whose next event needs what another participant did before the barrier (an
object that the other thread initialized, say) and whose last event is the barrier itself. -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- **A ready `bar.sync` has its generation completed**: the release condition is among its
needs. -/
theorem ctaBarDone_of_readyAt {e : EvId} {pc : Nat} (hbar : X.IsBarrier e id count pc)
    (hready : Ready L X e) : ∃ key, CtaBarK L X e key ∧ CtaBarDone L X (e.1 / L.block) key := by
  have hb : X.get e = some ⟨pc, .bar id count .sync⟩ := hbar
  have hmem : Need.cond (∃ key, CtaBarK L X e key ∧ CtaBarDone L X (e.1 / L.block) key) ∈
      Needs L X e := by
    simp only [Needs, hb, KindNeeds, ctaBarNeeds]
    exact List.mem_append_right _ List.mem_cons_self
  exact hready _ hmem

section
variable [hK : Fact K.NoBarArrive]

/-- **A ready `bar.sync` has released the generation of its ordinal.** -/
theorem Sources.ready_released (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} (hf : X.IsBarrier f id count pc)
    (hready : Ready L X f) :
    Released L.block (X.barriers (f.1 / L.block)) id
      (((X.tr f.1).take f.2).countP (Execution.isBarId id)) := by
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_readyAt hf hready
  have hk := hS.key hX hG hf hkey
  subst hk
  have h1 : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) % 16 = id := by
    have := hG.id_lt
    omega
  have h2 : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) / 16 =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
    have := hG.id_lt
    omega
  unfold CtaBarDone at hdone
  rw [h1, h2] at hdone
  exact hdone

/-- **A ready `bar.sync` has every participant's arrival of its ordinal**: a participant lane
of its CTA that never exits has made its arrival with as many earlier ones. -/
theorem Sources.ready_member_arrival (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id) (hG : Shape L count p id) {f : EvId} {pc : Nat}
    (hf : X.IsBarrier f id count pc) (hready : Ready L X f) {g : Nat}
    (hcta : g / L.block = f.1 / L.block) (hw : (g % L.block) / 32 ∈ p)
    (hno : ∀ j pcx, X.get (g, j) ≠ some ⟨pcx, .exit⟩) :
    ∃ i pc', X.IsBarrier (g, i) id count pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
  have hfg : f.1 < L.threads := by
    obtain ⟨key, hk, -⟩ := ctaBarDone_of_readyAt hf hready
    exact hk.1
  have hb0 : 0 < L.block := block_pos_of_thread_lt hfg
  have hthr : f.1 / L.block * L.block + g % L.block = g := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  have hno' : ∀ j pcx,
      X.get (f.1 / L.block * L.block + g % L.block, j) ≠ some ⟨pcx, .exit⟩ := by
    rw [hthr]
    exact hno
  obtain ⟨e, pc', he1, he, hcount, -⟩ := hS.member_key hX hG (cta_lt hfg)
    (hS.ready_released hX hG hf hready) (Nat.mod_lt g hb0) hw hno'
  have hge : e.1 = g := by rw [he1, hthr]
  obtain ⟨e1, e2⟩ := e
  simp only at hge
  subst hge
  exact ⟨e2, pc', he, hcount⟩

end

end
end PTX.NamedBar
