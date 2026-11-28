-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.OutKinds
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ni
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpPath
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpKinds
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpWindow
public import Kernels.InklingRelDecode.Proof.Lib.Alpha
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
import Kernels.InklingRelDecode.Proof.Softmax.Data.SwExp
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
public import Kernels.InklingRelDecode.Proof.Lib.WindowEntry
import Lemmas.Kernel.PostEvent
import Lemmas.Execution.TraceProjection


/-! # The state after the shuffle of pc 1838

A state of the lane that the local steps reach from the state after the shuffle of pc 1838, below
the shuffle of pc 2234, comes from a state at pc 1839 that holds the shuffle's words and the
window's registers (`exp_front`): the carried maximum and the two halves are numbers or `-inf`,
and the window's inputs are typed (`ExpIn`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Soft

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

public theorem exp_entry_ok : Lib.entryOk 1839 2234 = true := by decide +kernel

private theorem site_1838 (s : Site) (h : s.pc = 1838) : s = .shfl5 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The window from the shuffle of pc 1838**: a state of the lane between pcs 1839 and 2233
comes from the state after the shuffle, which holds its words and the window's inputs. -/
public theorem exp_front {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hl : Iface.LaneState L X g t) (hp1 : 1839 ≤ t.pc) (hp2 : t.pc < 2234) :
    ∃ (m sent recv : Value) (vH V : Nat → Value) (t0 : TState),
      SK.ni.Has m ∧ SK.ni.Has sent ∧ SK.ni.Has recv ∧ ExpIn V ∧
      (∀ r ∈ kE0, V r = if r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 then
        Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r else vH r) ∧
      At t0 1839 ([(1520, sent), (1521, recv), (1914, m), (498, scaleW L)] ++
        factsFrom kHx vH) ∧ Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t := by
  obtain ⟨k, t0, hr, ht⟩ := hl
  obtain ⟨k0, hk0, hr0⟩ : ∃ k0 ≤ (X.tr g).length,
      Run kernel Assumptions.all L g {} ((X.tr g).take k0) (some t0) := by
    by_cases h : k ≤ (X.tr g).length
    · exact ⟨k, h, hr⟩
    · refine ⟨_, le_rfl, ?_⟩
      rw [List.take_length]
      rwa [List.take_of_length_le (by omega)] at hr
  cases k0 with
  | zero =>
    rw [List.take_zero] at hr0
    cases hr0
    have := (Lib.rtg_pred (L := L) (g := g) (lo := 1839) (hi := 2234) exp_entry_ok ht hp1 hp2.le).1
    exact absurd this (by decide)
  | succ k' =>
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k']? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have get : X.get (g, k') = some e := he
    have hr1 := hr0
    rw [List.take_add_one, he, Option.toList_some] at hr0
    obtain ⟨u, s, -, -, hes⟩ := Run.unsnoc _ e hr0
    obtain ⟨hs1, -⟩ := Lib.win_entry exp_entry_ok hes ht hp1 hp2
    have hpe : e.pc = 1838 := by
      have := EventFrame.estep_source_pc hes
      omega
    have clean : ∀ f, e.kind ≠ .ub f := fun f h => by
      obtain ⟨m', -, hf'⟩ := hes
      exact fires_some_not_ub hf' e.pc f (by cases e; simp_all)
    obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean (by omega) (by omega)
    obtain ⟨s0, hs0, hse⟩ := value_state hsc
    obtain ⟨y, hy, rfl⟩ := softD_shape hse
    have len : k' ≤ (X.tr g).length := by omega
    have nub := Frame.noUbBefore_of_get hX get
    have lane : g % L.block < 128 := data_warp hp hX len hsc
    obtain ⟨typ, ni⟩ := soft_ni hp hX hf hS (h5 lane) k' len _ hs0 nub w ent y n rfl
    obtain ⟨sp, ins0, hat, -, -, hes'⟩ := Frame.post_event (C := threadD Q L)
      (fun g h => threadD_sound hp h) hX get hr1 hs0
    obtain ⟨hs2, ht0⟩ := Lib.win_entry exp_entry_ok hes' ht hp1 hp2
    obtain ⟨ins1, hc1, -, hf1⟩ := EventFrame.estep_event_source hes'
    have hsite : y.c.site = .shfl5 := by
      refine site_1838 _ ?_
      rw [← hy] at atpc
      omega
    change (Data.codeS ent L g).AtD y sp at hat
    have hpsp : sp.pc = 1838 := by omega
    rw [hpsp] at hc1 hf1
    obtain ⟨mode, sent, bv, cv, recv, ok, hev, hAt⟩ := shfl5_at hsite hat hc1 hf1
    obtain ⟨c', hnc⟩ : ∃ c', Control.next ent L g y.c e = some (some c') := by
      subst hev
      exact ⟨{ y.c with site := .shfl6 }, by simp [Control.next, hsite]⟩
    have hn : succ ent L g y e = some (some ⟨c', record L y e c'.site⟩) := by simp [succ, hnc]
    obtain ⟨typ', ni'⟩ := soft_ni_step hp hX hf hS (h5 lane) get clean (by rw [hpe, hsite]; rfl)
      hn ⟨typ, ni⟩
    subst hev
    obtain ⟨-, hm0, -, hV⟩ := xV_shfl5 hsite hn
    have hE := xV_expIn (e := ent) (L := L) (g := g) hp typ' (by rw [hm0]; exact ni.m) ni'.mx
    exact ⟨y.v.m, sent, recv, vHs ent L g y, _, t0, ni.m, (h5 lane k' _ sent bv cv recv ok get).1,
      (h5 lane k' _ sent bv cv recv ok get).2, hE, hV, hAt, ht⟩
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
