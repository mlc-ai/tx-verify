-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocObjectHistory
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.Execution.Legacy

@[expose] public section

/-! An appended control event and its object record do not change causality into an
older instruction when no old read reads from the new instruction (`SnocReadsOld`). The new
instruction must not be a barrier or release arrival. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref}

def Execution.snocObject (X : Execution) (g : Nat) (e : Event) (r : Nat → Option Ref)
    (mb : Loc) (rec : Record Ref) : Execution := (X.snoc g e r).appendObject mb rec

/-- An appended object record cannot affect an edge into an older thread event:
its observing wait is also old, hence it is not the appended record. -/
theorem snocObject_step_old (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r)
    (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g,(X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : po (X.snocObject g e r mb rec) a b ∨ CtaBarSync L (X.snocObject g e r mb rec) a b ∨
      MSync L (X.snocObject g e r mb rec) a b ∨ ClusterSync L (X.snocObject g e r mb rec) a b ∨
      WarpBarSync L (X.snocObject g e r mb rec) a b ∨ synchronizesWith L
          (X.snocObject g e r mb rec) a b ∨ FenceSync L (X.snocObject g e r mb rec) a b) :
    po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b := by
  have waitOld {w : EvId} (hw : w.1 = b.1) (hi : w.2 < b.2) : rec.id ≠ .thread w := by
    rw [hid]
    intro he
    have heq := Ref.thread.inj he
    subst w
    simp only at hw hi
    rw [← hw] at hbo
    omega
  have hs : po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨
      MSync L (X.snoc g e r) a b ∨ ClusterSync L (X.snoc g e r) a b ∨
      WarpBarSync L (X.snoc g e r) a b ∨ synchronizesWith L (X.snoc g e r) a b ∨
      FenceSync L (X.snoc g e r) a b := by
    rcases h with hp | hbar | hm | hc | hw | hmem | hfs
    · exact .inl hp
    · exact .inr (.inl hbar)
    · obtain ⟨x,w,m,rs,ws,hr,⟨ha,hu⟩,hsc,hwt,hwi,hlen,hxt,hxi⟩ := hm
      exact .inr (.inr (.inl
        ⟨x,w,m,rs,ws,hr,⟨ha,(appendObject_update_iff (waitOld hwt hwi)).mp hu⟩,hsc,hwt,hwi,hlen,
          hxt,hxi⟩))
    · exact .inr (.inr (.inr (.inl hc)))
    · exact .inr (.inr (.inr (.inr (.inl hw))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl hmem)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr hfs)))))
  exact snoc_step_old_full (fun mask inst he => by simp [Kind.Legacy,he] at hfree)
    hcl hold hnb hna (fun s he => by simp [Kind.Legacy,he] at hfree) hbo hs

theorem snocObject_baseCausality_old (hcl : ClusterHistoryOk L X)
    (hold : SnocReadsOld X g e r) (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g,(X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : baseCausality L (X.snocObject g e r mb rec) a b) : baseCausality L X a b := by
  induction h with
  | single h => exact .single (snocObject_step_old hcl hold hfree hid hnb hna hbo h)
  | tail _ h ih =>
    have hs := snocObject_step_old hcl hold hfree hid hnb hna hbo h
    exact (ih (baseCausality_events (Relation.TransGen.single hs)).1).tail hs

end
end PTX
