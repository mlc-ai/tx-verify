-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Mma
public import Kernels.InklingRelDecode.Proof.Mma.Export.Mbar
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Lemmas.Protocol.MbarRowSource
import Lemmas.Protocol.MbarRowKind

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX MbarRow PTX.MbarRow

private theorem commit_use {Q L m X g k pc l sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hw : g % L.block / 32 = 7) (he : X.get (g,k) = some ⟨pc,.tc (.commit sp)⟩)
    (hm : Frame.MbarOf ⟨pc,.tc (.commit sp)⟩ l) : MmaUse L X g k ⟨pc,.tc (.commit sp)⟩ l := by
  obtain ⟨off,rfl,h⟩ := commit hp hX hf hw he
  obtain ⟨rank,ht⟩ := hm
  unfold TcCommit.target at ht
  split at ht <;> try contradiction
  rename_i hr
  have hz : rank.val = 0 := by have : rank.val < 1 := hr.1; omega
  have hl := (Option.some.inj ht).symm
  simp only [hz,Nat.add_zero] at hl
  subst l
  let sp : TcCommit.Spec := ⟨.one, loc L g off, 1, g / L.block, 1⟩
  have cm : Commit ⟨pc,.tc (.commit sp)⟩ (loc L g off) := ⟨_,rfl,rfl,rfl⟩
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .sCommit rfl rfl cm
  · exact .emptyCommit rfl rfl cm
  · exact .doneCommit rfl rfl cm
  · exact .finalCommit rfl rfl cm

public theorem mbarRow {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : MbarRow.Mma Q L X := by
  intro g k e l _ he hat hm
  obtain ⟨hw,lo,hi⟩ := hat
  obtain ⟨s,hs,hpc,t,ins,u,ht,_,hop,fire⟩ := region_source mma_sites hX he hm lo hi
  rw [← ht] at fire
  have kinds : ∀ a ∈ mmaSites, a.shape = .commit ∨
      ((a.pc = 2462 ∨ a.pc = 2510) ∧
        (a.shape = .wait (.reg 545) ∨ a.shape = .wait (.reg 558))) := by decide
  obtain ⟨pc,kd⟩ := e
  rcases kinds s hs with h | ⟨hsite,h⟩
  · obtain ⟨sp,rfl⟩ := emits_commit (h ▸ hop) fire
    exact commit_use hp hX hf hw he hm
  · have hk : ∃ m q ok acq sc, kd = .wait m q ok acq sc := by
      rcases h with h | h <;> exact emits_wait (h ▸ hop) fire
    obtain ⟨obj,q,ok,acq,sc,rfl⟩ := hk
    obtain rfl : l = obj := hm
    change s.pc = pc at hpc
    obtain ⟨rfl,rfl,hp'⟩ := poll hp hX hf hw (hpc ▸ hsite) (.inl he)
    rcases hp' with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · exact .readyWait rfl rfl ⟨ok,rfl⟩
    · exact .pWait rfl rfl ⟨ok,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
