-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Region
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemSite
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax
variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat} {e : Event} {d : D}

theorem softState_event (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,i) = some e) (hs : softState p L X g i = some d) : EvS p L g d e := by
  unfold softState at hs
  split at hs
  · rename_i v n hd
    cases Option.some.inj hs
    exact (SmWarp.data_event hp hX (SmWarp.storeSafe hp g) he hd).1
  · cases hs

/-- The score credit stays fixed through all reads and stores of a round. -/
theorem soft_credit_step (hw : Prologue.warpIndex L g < 8) (he : X.get (g,i) = some e)
    (ev : EvS p L g d e) (off : pollOff d.site ≠ 80) :
    Tm.sPolls L X g (Prologue.warpIndex L g/4) (i+1) =
      Tm.sPolls L X g (Prologue.warpIndex L g/4) i := by
  let l := Tm.sFull L (g/L.block) (Prologue.warpIndex L g/4)
  obtain ⟨hi,eq⟩ := List.getElem?_eq_some_iff.mp he
  have no : okPoll l e = false := by
    unfold okPoll sourceWaitSuccess
    split
    · rename_i target par ac sc kind
      apply decide_eq_false
      intro h
      have hm : Frame.MbarOf e target := by cases e; cases kind; rfl
      rcases soft_mbar ev.1 hm with ⟨bad,_⟩ | ⟨_,_,_,addr,_⟩
      · rw [kind] at bad; cases bad
      · rw [bl_eq hw,h] at addr
        apply off
        have ha := congrArg Loc.addr addr
        change L.sharedBase + (80 + 8 * _) = L.sharedBase + (pollOff d.site + 8 * _) at ha
        omega
    · rfl
  unfold Tm.sPolls
  rw [List.take_succ_eq_append_getElem hi,eq,okPolls_snoc,no]
  rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Values
