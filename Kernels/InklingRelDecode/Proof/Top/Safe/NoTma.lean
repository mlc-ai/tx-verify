-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Protocol.Shared.OperandRead
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarFaults
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noTma (hp : Pre Q L m)
    {X : Execution} (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) : ¬ TmaUnsafe L m X := by
  have fault : ∀ c < L.grid, ∀ j : Fin 12, 6≤j.val → j.val<11 →
      ∀ r ∈ X.objects ⟨.shared,c,L.sharedBase+MbarRow.initOffset j⟩, ¬ r.fault.isSome := by
    intro c hc j low high r hr
    obtain ⟨o,off⟩ := Protocol.Scalar.slot_object j low high
    have loc : (⟨.shared,c,L.sharedBase+MbarRow.initOffset j⟩ : Loc)=o.loc L c := by
      simp only [Protocol.Scalar.Object.loc,off]
    rw [loc] at hr
    have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
    simp [Protocol.Scalar.fault_free hp hX hf rows init words hc o r hr]
  rintro (⟨l,r,hr,bad⟩|⟨l,r,hr,bad⟩|⟨e,a,w,i,l,c,b,intent,ini,hit,over,bad,_⟩|bulk|mask)
  · obtain ⟨c,hc,j,rfl⟩ := Protocol.Mbar.record_loc hX rows init hr
    by_cases scalar : 6≤j.val
    · by_cases recurrent : j.val<11
      · exact fault c hc j scalar recurrent r hr bad
      · obtain rfl : j=11 := Fin.ext (by have := j.isLt; change j.val=11; omega)
        have free := Protocol.OFinal.fault_free hp hX hf rows init (c := c) r hr
        simp [free] at bad
    · let s : Fin 3 := ⟨j.val/2,by omega⟩
      have ring := Protocol.KV.ready_slot hp hX hf rows init hc s
      have fits := Protocol.KV.slot_fits (Q := Q) (X := X) (L := L) (c := c) (s := s)
      have layout : ∀ i : Fin 12, i.val<6 → ∀ u : Fin 3, i.val/2=u.val →
          MbarRow.initOffset i=Iface.kvReady u ∨ MbarRow.initOffset i=Iface.kvEmpty u := by decide
      have addr := layout j (by omega) s rfl
      have free := SingleTmaRing.fault_free hX ring fits (r := r)
        (addr.imp (congrArg (fun off => Loc.mk .shared c (L.sharedBase+off)))
          (congrArg (fun off => Loc.mk .shared c (L.sharedBase+off)))) hr
      simp [free] at bad
  · exact bad (Protocol.Mbar.published hX rows init hr)
  · obtain ⟨pc,get⟩ := ini
    obtain ⟨j,_,rfl,_⟩ := Protocol.Mbar.init_info rows (Frame.lt_of_get hX get) get
    have ⟨space,_,lo,hi⟩ := over
    have bounds : ∀ j : Fin 12, 213216≤MbarRow.initOffset j ∧ MbarRow.initOffset j+8≤213336 :=
      by decide
    have off := bounds j
    dsimp [MbarRow.loc] at space lo hi
    exact Protocol.Shared.arena_clear hp hX hf intent hit space (by omega) (by omega)
  · exact not_cpAsyncOverlap_of_none (fun _ _ ⟨_,he⟩ _ => Lib.no_copy hX he) bulk
  · exact not_maskedRangeUnalloc_of_none (fun _ _ _ ⟨_,he⟩ _ => Lib.no_copy hX he) mask

end PTX.Kernels.InklingRelDecode.Proof.Top
