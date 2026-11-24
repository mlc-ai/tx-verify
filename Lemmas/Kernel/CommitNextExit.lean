-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # An unobserved commit arrive-on, finished through the next commit's

ERR-SHARED-LIFETIME's lifetime order has, besides the dependency order and one object's order,
the `CommitNext` step that a kernel assumption selects with `commitInOrder` (ASM-INTERFACE): from
the completion of the arrive-on of a selected `tcgen05.commit` at rank `r` to the start of the
arrive-on at rank `r` of the issuing thread's next commit. An arrive-on that no thread observes is
then finished once the next commit's arrive-on is witnessed by a wait followed by a dependency path
to an owner exit (`SharedFinished.of_commitNext`): the path runs from the selected arrive-on's
completion to the next arrive-on, then through its witness and the dependency path. -/

namespace PTX
open AsyncCopy

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- **The arrive-on of a selected commit is finished when the next commit's arrive-on at the same
rank is witnessed by a wait that precedes an owner exit.** -/
theorem SharedFinished.of_commitNext {i j w finish : EvId} {r : Fin 16} {c : Nat}
    (hi : X.RefPresent (.async i (.tcNotify r)))
    (hn : CommitNext A X (.async i (.tcNotify r)) (.async j (.tcNotify r)))
    (ho : Witness L X (.async j (.tcNotify r)) w)
    (h : Relation.TransGen (DepStep L K X) (.thread w, true) (.thread finish, false))
    (hx : OwnerExit L X c finish) : SharedFinished L K A X (.async i (.tcNotify r)) c :=
  SharedFinished.of_commit_next hi hn ho h hx

end

end PTX
