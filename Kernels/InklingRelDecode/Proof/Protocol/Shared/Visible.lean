-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Reuse
public import Kernels.InklingRelDecode.Proof.Lib.RoleWord
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Kernels.InklingRelDecode.Proof.Prologue.Export.Published
import Kernels.InklingRelDecode.Proof.Common.Export.Publisher
import Lemmas.Kernel.Safety.HandoffPhased

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof PTX.Frame

private theorem publisher_arrived {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2340 ∨ p=2345 ∨ p=2423) :
    ∃ v, X.get (g/L.block*L.block,v)=some ⟨573,.bar 1 none .sync⟩ := by
  have phase := Export.publication_read hp hX he site
  obtain ⟨j,q,cnt,md,jk,bar,ord⟩ := nth_bar (X := X) (id := 1) (g := g) (f := k) (q := 0) (by omega)
  obtain ⟨rfl,rfl⟩ := Lib.publication_kind hX hp.block bar
  have len : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have cta : g/L.block*L.block/L.block=g/L.block := Nat.mul_div_cancel _ (by rw [hp.block]; decide)
  obtain ⟨u,pc,ev,idx⟩ := member_sync hp hX bar (by omega) cta
  have actual := Export.first_data_sync hp hX ev (by rw [Nat.mul_mod_left]; decide) (idx.trans ord)
  exact ⟨u,actual ▸ ev⟩

/-- Each observed worker read has a same-CTA store for both count words, with
the complete launch-dependent payload and a causality edge into the read. -/
theorem visible_pair {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2340 ∨ p=2345 ∨ p=2423) (j : Fin 2) :
    ∃ u, X.get (g/L.block*L.block,u)=some ⟨571,.wr
      (Lib.wordAcc ⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ j.val)
      (b32 (if j=0 then Iface.preloadCount Q L (g/L.block) else
        Lib.blocksOf Q L (g/L.block))).toBytes⟩ ∧
      baseCausality L X (g/L.block*L.block,u) (g,k) := by
  obtain ⟨v,sync⟩ := publisher_arrived hp hX he site
  obtain ⟨u,_,store⟩ := Prologue.Export.published_pair hp hX sync j
  have cta : g/L.block*L.block/L.block=g/L.block := Nat.mul_div_cancel _ (by rw [hp.block]; decide)
  have order := publish_before_read hp hX store (.inr rfl) he site cta
  rw [cta] at store
  exact ⟨u,store,order⟩

/-- The first role word is visible before every dispatch or count-pair read. -/
theorem visible_role {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2340 ∨ p=2345 ∨ p=2423) :
    ∃ u, X.get (g/L.block*L.block,u)=some ⟨570,.wr
      (Lib.wordAcc ⟨.shared,g/L.block,L.sharedBase+213336⟩) (b32 16777730).toBytes⟩ ∧
      baseCausality L X (g/L.block*L.block,u) (g,k) := by
  obtain ⟨v,sync⟩ := publisher_arrived hp hX he site
  obtain ⟨u,acc,bytes,_,store⟩ := Prologue.Export.published_role hp hX sync
  have cta : g/L.block*L.block/L.block=g/L.block := Nat.mul_div_cancel _ (by rw [hp.block]; decide)
  have order := publish_before_read hp hX store (.inl rfl) he site cta
  obtain ⟨loc,val⟩ := Lib.role_word hp hX store (.inl ⟨rfl,rfl⟩)
  rw [loc,val,cta] at store
  exact ⟨u,store,order⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
