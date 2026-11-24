-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ReachJoint

/-! # Two objects that gate each other, by the joint induction

A commit object `mN` (one committing thread `c`, its view `m0`) and a unit object `mU` (producers
`prod a`, consumer `c`), the shape of an S-full/P-ready pair: `c` commits use `t` after `t` uses
of `mU` (`hC`), and each producer arrives with use `u` after `u + 1` uses of `mN` (`hP`). Both
objects' reuse paths follow from these two route facts alone, by `Reach.joint` over the family
`UnitAt` (consumer `c`) and `NotifyAt` (each producer), with the content of the polls inside the
induction (`unit_content`, `notify_content`). -/

namespace PTX.Tests.ReachJoint
open PTX PTX.Flow PTX.MbarRing PTX.MbarRing.Reach AsyncCopy

example {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {mU mN m0 : Loc} {N δU δN c : Nat} {prod : Fin N → Nat}
    (OU : Unit.Obj X mU N prod δU) (ON : Notify.Obj X mN c m0 δN)
    (hC : ∀ {i pc sp}, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = m0 →
      ((X.tr c).take i).countP (commitsTo m0) + δU ≤ okPolls mU ((X.tr c).take i))
    (hP : ∀ {a i pc sc}, X.get (prod a, i) = some ⟨pc, .arrive mU 0 1 true sc⟩ →
      arrivals mU ((X.tr (prod a)).take i) + δN + 1 ≤ okPolls mN ((X.tr (prod a)).take i)) :
    Unit.Reach L K A X mU N prod δU c ∧ ∀ a, Notify.Reach L K A X mN c m0 δN (prod a) := by
  let G : Option (Fin N) → Ref × Bool → Prop := fun
    | none => UnitAt L K X mU N prod δU c
    | some a => NotifyAt L K X mN c m0 δN (prod a)
  have hall := joint hX G fun n hn ih => by
    have ihU : ∀ n' ∈ nodes L X, Relation.TransGen (DepStep L K X) n' n →
        UnitAt L K X mU N prod δU c n' := fun n' h1 h2 => ih n' h1 h2 none
    have ihN : ∀ a, ∀ n' ∈ nodes L X, Relation.TransGen (DepStep L K X) n' n →
        NotifyAt L K X mN c m0 δN (prod a) n' := fun a n' h1 h2 => ih n' h1 h2 (some a)
    rintro (_ | b)
    · -- a producer's arrival of use `t`: through the commit of use `j + 1`
      intro x hx hn' j hj
      subst hn'
      obtain ⟨-, ⟨pc, sc, hget⟩, harr⟩ := OU.S_rec hx
      change X.get (prod x.1, nthEv X (arrivesOn mU) (prod x.1) x.2) = _ at hget
      change arrivals mU ((X.tr (prod x.1)).take (nthEv X (arrivesOn mU) (prod x.1) x.2)) =
        x.2 at harr
      show Relation.TransGen (DepStep L K X) _
        ((Ref.thread (prod x.1, nthEv X (arrivesOn mU) (prod x.1) x.2)), false)
      set i := nthEv X (arrivesOn mU) (prod x.1) x.2
      have hlen : i < (X.tr (prod x.1)).length := len_of_get hget
      have hpa := hP hget
      rw [harr] at hpa
      have hpoll : (j + 1) + δN < okPolls mN (X.tr (prod x.1)) := by
        have := Poll.okPolls_mono mN (X.tr (prod x.1)) hlen.le
        rw [List.take_of_length_le (le_refl _)] at this
        omega
      have hg1 := poll_guard (L := L) hspin (m := mN) (n := (j + 1) + δN) hlen (by omega)
      obtain ⟨hS, hw⟩ := notify_content hX ON hspin hpoll (.single hg1) (ihN x.1)
      obtain ⟨⟨k, r, hk, hid, -, -⟩, pc', sp, hcm, hmb, -, hcnt⟩ := ON.S_rec hS
      dsimp only at hk hid hcm hcnt hw
      obtain ⟨-, -, -, -, hrk⟩ := notify_rec hX (List.mem_of_getElem? hk) hid
      have hc := hC hcm hmb
      rw [hcnt] at hc
      have hcl : Notify.cm X c m0 _ < (X.tr c).length := len_of_get hcm
      exact .head (poll_guard hspin hcl (by omega))
        (.head (commit_notify hcm hrk) (.head (DepStep.of_witness L hw) (.single hg1)))
    · -- a notification of the commit of use `t`: through the arrival of use `j`
      intro x hx hn' j hj
      subst hn'
      obtain ⟨⟨k, r, hk, hid, -, -⟩, pc, sp, hcm, hmb, -, hcnt⟩ := ON.S_rec hx
      show Relation.TransGen (DepStep L K X) _ (Ref.async (c, Notify.cm X c m0 x.2)
        (.tcNotify (Notify.rank X mN c m0 x.2)), false)
      obtain ⟨-, -, -, -, hrk⟩ := notify_rec hX (List.mem_of_getElem? hk) hid
      have hc := hC hcm hmb
      rw [hcnt] at hc
      have hcl : Notify.cm X c m0 _ < (X.tr c).length := len_of_get hcm
      have hpoll : j + δU < okPolls mU (X.tr c) := by
        have := Poll.okPolls_mono mU (X.tr c) hcl.le
        rw [List.take_of_length_le (le_refl _)] at this
        omega
      have hn1 := commit_notify (L := L) (K := K) hcm hrk
      have hg1 := poll_guard (L := L) hspin (m := mU) (n := j + δU) hcl (by omega)
      obtain ⟨hS, hw⟩ := unit_content hX OU hspin hpoll ((Relation.TransGen.single hg1).tail hn1)
        ihU b
      obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := OU.S_rec hS
      change X.get (prod b, nthEv X (arrivesOn mU) (prod b) j) = _ at hga
      change arrivals mU ((X.tr (prod b)).take (nthEv X (arrivesOn mU) (prod b) j)) = j at harr
      change Witness L X (.thread (prod b, nthEv X (arrivesOn mU) (prod b) j)) _ at hw
      generalize nthEv X (arrivesOn mU) (prod b) j = ia at hga harr hw
      have hpa := hP hga
      rw [harr] at hpa
      exact .head (poll_guard hspin (len_of_get hga) (by omega))
        (.head (DepStep.of_witness L hw) ((Relation.TransGen.single hg1).tail hn1))
  exact ⟨unit_reach hX OU (hall none), fun a => notify_reach hX ON (hall (some a))⟩

end PTX.Tests.ReachJoint
