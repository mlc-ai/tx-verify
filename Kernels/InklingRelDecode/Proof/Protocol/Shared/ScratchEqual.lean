-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleInduction
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

/-- **The scratch stores of one warp in one round are equal**: two stores of pc 2250 by lanes of
one warp, at one barrier-zero ordinal after the same number of optional rendezvous, write the same
bytes (every lane stores the minimum the warp's butterfly computed). -/
def WarpStoresEqual (L : Launch) (X : Execution) : Prop :=
  ∀ {h u t v dst ys acc zs}, X.get (h,u)=some ⟨2250,.wr dst ys⟩ →
    X.get (t,v)=some ⟨2250,.wr acc zs⟩ → h/L.block=t/L.block → h%L.block/32=t%L.block/32 →
    h%L.block<128 → barOrdinal X h u=barOrdinal X t v →
    ((X.tr h).take u).countP (fun e => e.pc==2326)=((X.tr t).take v).countP (fun e => e.pc==2326) →
    ys=zs

/-- Two stores of one warp at one ordinal are equal once the rounds below it agree. -/
theorem stores_equal {Q L m X h u t v dst ys acc zs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (equal : WarpStoresEqual L X)
    (agree : ∀ n<barOrdinal X h u, StoreAgree L X n) (one : X.get (h,u)=some ⟨2250,.wr dst ys⟩)
    (two : X.get (t,v)=some ⟨2250,.wr acc zs⟩) (cta : h/L.block=t/L.block)
    (warp : h%L.block/32=t%L.block/32) (ord : barOrdinal X h u=barOrdinal X t v) : ys=zs := by
  have lh := data_site hp hX one (by simp) (by dsimp; decide) (by dsimp; decide)
  have lt := data_site hp hX two (by simp) (by dsimp; decide) (by dsimp; decide)
  have uni := rescale_agree_by hp hX hf agree one (by simp) rfl rfl lh
  have visits := visits_equal hp hX one two cta.symm lt ord.symm
    (fun h' ch lh' n' lt' => uni h' h ch lh' rfl lh n' lt')
  exact equal one two cta warp lh ord visits.symm

/-- **Every round's stores agree**, by induction on the barrier-zero ordinal: the lanes agree on the
optional rendezvous below the ordinal (`rescale_agree_by`, from the agreement of the earlier
rounds), so two stores of one word have equal bytes. -/
theorem store_agree {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (equal : WarpStoresEqual L X) (n : Nat) : StoreAgree L X n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h u t v dst ys acc zs l one two oh ot ne hit hit' _ _ _
    have lh := data_site hp hX one (by simp) (by dsimp; decide) (by dsimp; decide)
    have lt := data_site hp hX two (by simp) (by dsimp; decide) (by dsimp; decide)
    obtain ⟨wl,ws⟩ := scratch_store hp hX one
    obtain ⟨wl',ws'⟩ := scratch_store hp hX two
    obtain ⟨_,c1,lo1,hi1⟩ := hit
    obtain ⟨_,c2,lo2,hi2⟩ := hit'
    rw [wl] at c1 lo1 hi1
    rw [wl'] at c2 lo2 hi2
    rw [ws] at hi1
    rw [ws'] at hi2
    dsimp only at c1 c2 lo1 lo2 hi1 hi2
    exact stores_equal hp hX hf equal (fun m lt' => ih m (by omega)) one two (c1.symm.trans c2)
      (by omega) (oh.trans ot.symm)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
