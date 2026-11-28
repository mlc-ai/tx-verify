-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BarRound
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchPublish
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleInduction
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleOrdinal
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedLanes
import Kernels.InklingRelDecode.Proof.Softmax.Export.PhysicalBar

@[expose] public section

/-! # A mandatory rendezvous of one data lane has a peer of the same round in every other

The rendezvous is a counted barrier of the four data warps: every data lane of the CTA that has not
exited meets it at the same barrier-zero ordinal. By the barrier schedule (`Uniform`) the peer is at
the same mandatory rendezvous of the same round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Frame Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem exit_site (pc : Nat) (h : pc = 2241 ∨ pc = 2251 ∨ pc = 999 ∨ pc = 1012) :
    Lib.afterFinal pc = 0 ∧ Lib.finalSync pc = false := by
  rcases h with rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩

/-- **A mandatory rendezvous of a data lane that has passed it has a peer of the same round in
every other data lane of its CTA.** -/
public theorem peer_bar (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) {t jb h pc c}
    (hpc : pc = 2241 ∨ pc = 2251 ∨ pc = 999 ∨ pc = 1012)
    (bar : X.get (t,jb) = some ⟨pc,.bar 0 c .sync⟩) (passed : jb+1 < (X.tr t).length)
    (lt : t%L.block < 128) (lh : h%L.block < 128) (cta : h/L.block = t/L.block) :
    ∃ ih c', X.get (h,ih) = some ⟨pc,.bar 0 c' .sync⟩ ∧ barOrdinal X h ih = barOrdinal X t jb ∧
      pollRound 1257 ((X.tr h).take ih) = pollRound 1257 ((X.tr t).take jb) ∧
      pollRound 2239 ((X.tr h).take ih) = pollRound 2239 ((X.tr t).take jb) := by
  obtain ⟨early,other⟩ := exit_site pc hpc
  obtain ⟨ih,p',c',hb,ord⟩ := data_arrival hp hX (show X.IsBarrier (t,jb) 0 c pc from bar)
    passed lt lh cta (fun k p ex => exit_ordinal hp hX bar (fun _ => nofun) early other ex lt lh
      cta.symm)
  have hb2 : X.get (h,ih) = some ⟨p',.bar 0 c' .sync⟩ := hb
  have isb := Protocol.Bar.zero_count_isBar hp hX hf safe cta lh lt hb2 bar ord
  have pcs : p' = pc := Protocol.Bar.data_bar_agree hp hX hf safe cta lh lt hb2 bar
    (by simp [Execution.isBar]) (by simp [Execution.isBar]) isb
  subst pcs
  have uni := rescale_agree hp hX hf safe bar (fun _ => nofun) early other lt
  have visits := visits_equal hp hX bar hb2 cta lh ord
    (fun a ca la n' hn' => uni a t ca la rfl lt n' hn')
  have lo : 574 < p' := by omega
  have hi : p' < 2331 := by omega
  have px := Softmax.Export.physical_bar hp hX bar (by simp) lo hi
  have py := Softmax.Export.physical_bar hp hX hb2 (by simp) lo hi
  rw [cta] at py
  dsimp only at px py
  have mand : Softmax.Export.mandatory ((X.tr h).take ih) =
      Softmax.Export.mandatory ((X.tr t).take jb) := by
    have o : ((X.tr h).take ih).countP (Execution.isBarId 0) =
        ((X.tr t).take jb).countP (Execution.isBarId 0) := ord
    omega
  obtain ⟨i,a1,a2,a3⟩ := bar_round_facts hp hX hf bar hpc
  obtain ⟨i',b1,b2,b3⟩ := bar_round_facts hp hX hf hb2 hpc
  have ii : i' = i := by omega
  subst ii
  exact ⟨ih,c',hb2,ord,by omega,by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
