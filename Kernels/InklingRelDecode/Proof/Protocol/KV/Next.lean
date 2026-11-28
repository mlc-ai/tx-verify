-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Ready
public import Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched MbarRow

private theorem site_warp {Q L X g k r l q ok ac sc} (rows : MbarRows Q L X)
    (hg : g < L.threads) (he : X.get (g,k) = some ⟨Ring.site r,.wait l q ok ac sc⟩) :
    g % L.block / 32 = r.warp := by
  have h := rows.place hg he (l := l) rfl
  cases r <;> simp only [StartupAt,PrologueAt,SoftmaxAt,EpilogueAt,DispatchAt,LoaderAt,MmaAt,
    Ring.site,Ring.warp] at * <;> omega

/-- The witness shares exactly the waiter's prefix, including its successful poll counts. -/
theorem next_slot {Q L m X g r l q ok ac sc}
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (hn : NextEv L kernel Assumptions.all m X g ⟨Ring.site r,.wait l q ok ac sc⟩) :
    ∃ s : Fin 3, l = r.obj L (g / L.block) s ∧
      q % 2 = (okPolls l (X.tr g) + (match r with
        | .ready => 0 | .empty => 1 - preload Q L (g / L.block) s)) % 2 := by
  obtain ⟨Y,hY,hprefix,he⟩ := hn
  have hg := Frame.lt_of_get hY he
  have hw := site_warp (rows Y hY) hg he
  obtain rfl := at_slot (rows Y hY) hg hw he
  refine ⟨_,rfl,?_⟩
  have hh := wait_parity (rows Y hY) hg he
  cases r <;> dsimp only at hh ⊢ <;> exact hh.trans (by rw [hprefix])

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
