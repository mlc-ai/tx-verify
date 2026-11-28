-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Lemmas.Protocol.NamedBarSources

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Alloc
open PTX

/-- **An mbarrier operand is an object of the arena of a launched CTA**: the user has an
initializer, and the initializers are the twelve objects of their CTA. -/
theorem mbar_operand {Q L m' X e m} (hX : Consistent L kernel Assumptions.all m' X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (hu : X.UsesMbar e m) :
    ∃ c < L.grid, ∃ j : Fin 12, m = ⟨.shared,c,L.sharedBase+MbarRow.initOffset j⟩ := by
  obtain ⟨ev,he,hm⟩ := Frame.usesMbar_mbarOf hu
  have ⟨v,n,hv⟩ : ∃ v n, X.MbInit v m n := by
    by_cases ini : ∃ n, ev.kind = .mbInit m n
    · obtain ⟨n,eq⟩ := ini
      obtain ⟨pc,k⟩ := ev
      cases eq
      exact ⟨e,n,pc,he⟩
    · obtain ⟨v,n,hv,_⟩ := init.publication he hm (fun n h => ini ⟨n,h⟩)
      exact ⟨v,n,hv⟩
  obtain ⟨pc,get⟩ := hv
  obtain ⟨j,_,rfl,_⟩ := Mbar.init_info rows (Frame.lt_of_get hX get) get
  exact ⟨_,NamedBar.cta_lt (Frame.lt_of_get hX get),j,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Alloc
