-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Reuse
import Kernels.InklingRelDecode.Proof.Common.Export.Publisher
import Lemmas.Kernel.Safety.HandoffPhased

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof PTX.Frame

/-- The preceding barrier generation of a worker read must also have
arrived on lane zero. This bounds dispatch before interpreting the role byte. -/
theorem read_round {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.rd a bs⟩)
    (site : pc=2340 ∨ pc=2345 ∨ pc=2423) :
    let n := ((X.tr g).take k).countP (Execution.isBarId 1)
    n=1 ∨ (n=4 ∧ ∃ v, X.get (g/L.block*L.block,v)=some ⟨2849,.bar 1 none .sync⟩) := by
  let n := ((X.tr g).take k).countP (Execution.isBarId 1)
  have phase : n%3=1 := Export.publication_read hp hX he site
  have prev : n-1<n := by omega
  obtain ⟨j,p,cnt,md,jk,bar,ord⟩ := nth_bar (X := X) (id := 1) (g := g) (f := k) prev
  obtain ⟨rfl,rfl⟩ := Lib.publication_kind hX hp.block bar
  have len : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have cta : g/L.block*L.block/L.block=g/L.block := Nat.mul_div_cancel _ (by rw [hp.block]; decide)
  obtain ⟨v,r,sync,idx⟩ := member_sync hp hX bar (by omega) cta
  have sites := Export.data_sync hp hX sync (by rw [Nat.mul_mod_left]; decide)
  rw [idx,ord] at sites
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at sites
  change n=1 ∨ (n=4 ∧ _)
  rcases sites with ⟨_,a⟩|⟨_,a⟩|⟨_,a⟩|⟨rfl,a⟩
  · exact .inl (by omega)
  · omega
  · omega
  · exact .inr ⟨by omega,v,sync⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
