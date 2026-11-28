-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Proof.Softmax.Export.NoUbLane
public import Kernels.InklingRelDecode.Proof.Epilogue.Export.NoUbLane
import Kernels.InklingRelDecode.Proof.Prologue.Export.SoftStart
import Kernels.InklingRelDecode.Proof.Prologue.Export.EntryTags
import Kernels.InklingRelDecode.Proof.Common.Export.BcastWord
import Kernels.InklingRelDecode.Proof.Softmax.Export.LateSingles
import Kernels.InklingRelDecode.Proof.Top.Safe.LateRcp

@[expose] public section

/-! # No data lane has undefined behaviour at a pc from 574 on

The lane's first event from 574 on is preceded by its event at 573 (`soft_start`), after which the
registers are typed (`entry_tags`). An undefined-behaviour event below 2565 is the softmax's
(`Softmax.Export.noUb_soft`); from 2565 on the lane's first epilogue event gives the epilogue's
entry (`Softmax.Export.epi_entry`), and the epilogue's window excludes it
(`Epilogue.Export.noUb_epi`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Flow.TyG PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **A data lane has no undefined-behaviour event at a pc from 574 on.** -/
theorem Safe.noUbLate {X : Execution} {g : Nat} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : Iface.BaseRead L X) (hv : Iface.LateValues L X)
    (lane : g % L.block < 128) {k pc : Nat} {f : Fault}
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hpc : 574 ≤ pc) : False := by
  have nu := Frame.noUbBefore_of_get hX he
  have hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = b32 (g % L.block / 32) := fun n P w hP hs => Export.bcast_names hp hX hf hP hs lane
  have hld : ∀ i a bs, X.get (g, i) = some ⟨2252, .rd a bs⟩ → ∃ v, rebuild 3 bs = .ok v :=
    fun _ _ _ h => (hv.ld h lane).imp fun _ h => h.1
  classical
  have hP : ∃ i, ∃ ev, X.get (g, i) = some ev ∧ 574 ≤ ev.pc := ⟨k, _, he, hpc⟩
  obtain ⟨e0, h0, hge0⟩ := Nat.find_spec hP
  have hi0k : Nat.find hP ≤ k := Nat.find_min' hP ⟨_, he, hpc⟩
  obtain ⟨j, hj, ej, hej, h573⟩ := Prologue.Export.soft_start hp hX hf base lane h0 hge0
    (fun i hi => nu i (by omega))
  have hE : ∀ t0 t1 u, Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0) →
      TauStar kernel Assumptions.all L g t0 t1 →
      EStep kernel Assumptions.all L g t1 ej (some u) →
      u.pc = 574 ∧ u.fault = none ∧ TypedF Iface.entryEnv u := fun t0 t1 u hr hs hes =>
    Prologue.Export.entry_tags hp hX hf base lane hej h573 (fun i hi => nu i (by omega)) hr hs hes
  by_cases hs : pc < 2565
  · exact Softmax.Export.noUb_soft hp hX hf base hv lane hnames hld (by omega) hej he hs hE
  have hs' : 2565 ≤ pc := by omega
  have hQ : ∃ i, ∃ ev, X.get (g, i) = some ev ∧ 2565 ≤ ev.pc := ⟨k, ⟨pc, .ub f⟩, he, hs'⟩
  obtain ⟨ei, hei, hgei⟩ := Nat.find_spec hQ
  have hik : Nat.find hQ ≤ k := Nat.find_min' hQ ⟨⟨pc, .ub f⟩, he, hs'⟩
  have hi0i : Nat.find hP ≤ Nat.find hQ := Nat.find_min' hP ⟨ei, hei, by omega⟩
  obtain ⟨R, hRP, hS, hrcp⟩ := Softmax.Export.late_package hv lane
  have hat := Softmax.Export.epi_entry hp hX hf base hv lane hnames hld
    (by omega : j < Nat.find hQ) hej hei hgei (fun i' ev h1 h2 hev => by
      by_contra hc
      exact Nat.find_min hQ h2 ⟨ev, hev, by omega⟩) hE
  exact Epilogue.Export.noUb_epi hp hX hf hv lane hRP (rcpStep_of hrcp)
    hS hnames hik hat he

end PTX.Kernels.InklingRelDecode.Proof.Top
