-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFBraS
public import Lemmas.Flow.SegQPre
public import Lemmas.Flow.SegQFH

@[expose] public section

/-! # A branch on a predicate register of the tag table, both arms to one end

The guard `@p` of a branch whose register the table types as a predicate: the register holds a
predicate, whose value is not known; the span of each arm reaches the same facts. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- Both arms of the branch `@p bra target` reach the end facts `G` (the lane's invariant). -/
theorem SegQF.braB {qt : Nat → EnvF} {R : TState → Prop} {pc target p b : Nat} {uni : Bool}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hlk : (qt pc).lookup p = some (.old .pred))
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq1 : tagsSatF (qt target) (qt pc) = true) (hq2 : tagsSatF (qt (pc + 1)) (qt pc) = true)
    (h1 : SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) target F b G)
    (h2 : SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) (pc + 1) F b G) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F b G := by
  intro t ht hQ
  have hT : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ.1
  obtain ⟨q, hreg⟩ : ∃ q, t.regs p = some (.pred q) := by
    simpa [TagF.ok, Tagged.Tag.ok] using hT p _ hlk
  have ht' : At t pc ((p, .pred q) :: F) := ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, hreg, ht.2.2.2.2⟩
  cases q with
  | false =>
    exact ((SegQ.tauAll R (SegQF.braPS (qt := qt) (F := (p, .pred false) :: F) false hc
      (fun _ hR => holds_mem hR (List.mem_cons_self ..)) hL hA hq2)).comp
      ((SegQ.weaken fun _ hR => holds_of_forall fun r hr =>
      holds_mem hR (List.mem_cons_of_mem _ hr)).comp h2)) t ht' hQ
  | true =>
    exact ((SegQ.tauAll R (SegQF.braPS (qt := qt) (F := (p, .pred true) :: F) true hc
      (fun _ hR => holds_mem hR (List.mem_cons_self ..)) hL hA hq1)).comp
      ((SegQ.weaken fun _ hR => holds_of_forall fun r hr =>
      holds_mem hR (List.mem_cons_of_mem _ hr)).comp h1)) t ht' hQ
end PTX.Flow.TyG
