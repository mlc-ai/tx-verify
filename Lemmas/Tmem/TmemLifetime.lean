-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Tcgen05.TcFence

@[expose] public section

namespace PTX
noncomputable section
variable {L : Launch} {X : Execution}

/-- Reallocation at the same numeric columns cannot revive a writer from the
preceding lifetime. The argument works for either peer's release attempt. -/
theorem TcMma.SourceLive.no_release_between {x e d : EvId} {cell : TcMma.Cell}
    {cta : Nat} {r : Tmem.Pair.Requests}
    (h : TcMma.SourceLive L X x e cell)
    (hac : ∀ n, ¬ Relation.TransGen (TcMma.TcStep L X) n n)
    (hr : r ∈ X.tmemHistory cta) (hc : Tmem.Pair.Covers L X r cell.cta e cell.column)
    (hd : Tmem.Pair.ReleaseOf L X r d)
    (hxd : baseCausality L X x d) (hde : baseCausality L X d e)
    (hk : (∃ a v sh, X.TLd e a v sh) ∨ (∃ a v sh, X.TSt e a v sh) ∨ X.TcAsync e) : False := by
  rcases h cta r hr hc d hd with hed | hdx
  · exact hac _ ((hed.tcStep hk).tail (.inl hde))
  · exact hac _ (.single (.inl (hxd.trans hdx)))

end
end PTX
