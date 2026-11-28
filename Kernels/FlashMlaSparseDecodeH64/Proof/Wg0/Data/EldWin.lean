-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.SegLib
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictEld
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiFacts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Epi
public import Lemmas.Flow.SegFrameSet
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018

@[expose] public section

/-! # The strict window after the row-sum read (pcs 1158 to the LSE store or the poll)

The final sum (pc 1158, a value run), the row guard (pcs 1159-1161, exact control), and then either
the logarithm's run (pcs 1162-1166) and the control stretch to the LSE store (pc 1178), or the
control stretch over them to the poll (pc 1184). The data facts are framed over the control
stretches and the control facts over the runs. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

theorem holds_swap {R : Nat → Option Value} {A B : List (Nat × Value)} (h : Holds R (A ++ B)) :
    Holds R (B ++ A) := by
  rw [holds_append] at h ⊢
  exact ⟨h.2, h.1⟩

/-- The final sum's run (pc 1158), framed over control facts `Hc`. -/
theorem eldRun3 (L : Launch) (g : Nat) (V : Nat → Value) (pe : Value) (Hc : List (Nat × Value))
    (hk : Hc.map Prod.fst = Control.ctlLive 1159) (c3 : Gen.e3_cond (f_ex1 V pe)) :
    ∃ n, Seg kernel Assumptions.all L g n 1158 (Gen.e3_facts0 (f_ex1 V pe) ++
      ([(481, f_ex1 V pe 481), (2880, f_ex1 V pe 2880)] ++ Hc)) 1159 (f_ew V pe ++ Hc) :=
  ⟨_, ((SegD.frame (H := [(481, f_ex1 V pe 481), (2880, f_ex1 V pe 2880)] ++ Hc) rulesFrame
    (Gen.e3_run L g (f_ex1 V pe)) rfl (by kernel_rfl)
    (by rw [List.map_append, hk]; kernel_rfl) fun _ _ => w0SegFree _).seg c3).weaken_end
    fun _ h => by simpa only [f_ew, List.append_assoc] using h⟩

/-- The logarithm's run (pcs 1162-1166), framed over control facts `Hc`. -/
theorem eldRun4 (L : Launch) (g : Nat) (V : Nat → Value) (pe : Value) (Hc : List (Nat × Value))
    (hk : Hc.map Prod.fst = Control.ctlLive 1167) (c4 : Gen.e4_cond (lookupD (f_ew V pe))) :
    ∃ n, Seg kernel Assumptions.all L g n 1162 (f_ew V pe ++ Hc) 1167 (f_lse V pe ++ Hc) :=
  ⟨_, ((SegD.frame (H := f_ew V pe ++ Hc) rulesFrame (Gen.e4_run L g (lookupD (f_ew V pe)))
    rfl (by kernel_rfl) (by rw [List.map_append, hk]; kernel_rfl)
    fun _ _ => w0SegFree _).seg c4).weaken_start (fun _ h => (holds_append _ _ _).mpr
      ⟨holds_lookupD (live := [481, 482]) ((holds_append _ _ _).mp h).1 (by kernel_rfl), h⟩)
    |>.weaken_end fun _ h => by simpa only [f_lse, List.append_assoc] using h⟩

/-- The start of the window: the facts of the final sum's run and the control facts at pc 1159. -/
theorem eld_start (d : Control.D) (hs : d.site = .eld) (V : Nat → Value) (pe : Value) :
    ∀ R, Holds R ((Control.facts P L g w d ++ f_exit V) ++ [(1728, pe)]) →
      Holds R (Gen.e3_facts0 (f_ex1 V pe) ++ ([(481, f_ex1 V pe 481), (2880, f_ex1 V pe 2880)] ++
        factsFrom (Control.ctlLive 1159) (Control.valueOf P L g w d))) := by
  intro R h
  obtain ⟨⟨hC, hD⟩, hP⟩ := (holds_append _ _ _).mp h |>.imp_left (holds_append _ _ _).mp
  have hD' : Holds R (f_exit V ++ [(1728, pe)]) := (holds_append _ _ _).mpr ⟨hD, hP⟩
  refine (holds_append _ _ _).mpr ⟨holds_lookupD (live := [1727, 1728]) hD' (by kernel_rfl),
    (holds_append _ _ _).mpr ⟨holds_lookupD (live := [481, 2880]) hD' (by kernel_rfl), ?_⟩⟩
  have hpc : d.site.pc = 1157 := by rw [hs]; rfl
  unfold Control.facts at hC
  rw [hpc] at hC
  exact holds_factsFrom_mono hC (by decide +kernel)

/-- **The window of the row-sum read, the head inside the heads**: to the LSE store. -/
theorem eldWinF (hp : Pre P L m) (d : Control.D) (hs : d.site = .eld) (V : Nat → Value)
    (pe : Value) (hb : scmp .ge .s (Control.r5W L g) (pw 64) = false)
    (c3 : Gen.e3_cond (f_ex1 V pe))
    (c4 : Gen.e4_cond (lookupD (f_ew V pe))) :
    ∃ n, Seg kernel Assumptions.all L g n 1158
      ((Control.facts P L g w d ++ f_exit V) ++ [(1728, pe)]) 1178
      (factsFrom (Control.ctlLive 1178) (Control.valueOf P L g w d) ++ f_lse V pe) := by
  obtain ⟨n1, h1⟩ := eldRun3 L g V pe (factsFrom (Control.ctlLive 1159)
    (Control.valueOf P L g w d)) factsFrom_keys c3
  obtain ⟨n2, h2⟩ := Control.eldSegSF (w := w) hp d hb
  obtain ⟨n3, h3⟩ := eldRun4 L g V pe (factsFrom (Control.ctlLive 1167)
    (Control.valueOf P L g w d)) factsFrom_keys c4
  obtain ⟨n4, h4⟩ := Control.lseSegS (w := w) hp d
  have h2' := Seg.frameSet (H := f_ew V pe) rulesFrame (S :=
    [1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172,
      1173, 1174, 1175, 1176, 1177, 1179, 1180, 1181, 1182, 1183])
    (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) h2
  have h4' := Seg.frameSet (H := f_lse V pe) rulesFrame (S :=
    [1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177])
    (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) h4
  refine ⟨n1 + (n2 + (n3 + n4)), ((h1.weaken_start (eld_start d hs V pe)).comp
    ((h2'.weaken_start fun _ h => holds_swap h).comp
    ((h3.weaken_start fun R h => ?_).comp (h4'.weaken_start fun _ h => holds_swap h))))⟩
  obtain ⟨hc, hd⟩ := (holds_append _ _ _).mp h
  exact (holds_append _ _ _).mpr ⟨hd, holds_factsFrom_mono hc (by decide +kernel)⟩

/-- **The window of the row-sum read, the head beyond the heads**: to the poll. -/
theorem eldWinT (hp : Pre P L m) (d : Control.D) (hs : d.site = .eld) (V : Nat → Value)
    (pe : Value) (hb : scmp .ge .s (Control.r5W L g) (pw 64) = true)
    (c3 : Gen.e3_cond (f_ex1 V pe)) :
    ∃ n, Seg kernel Assumptions.all L g n 1158
      ((Control.facts P L g w d ++ f_exit V) ++ [(1728, pe)]) 1184
      (factsFrom (Control.ctlLive 1184) (Control.valueOf P L g w d) ++ f_ew V pe) := by
  obtain ⟨n1, h1⟩ := eldRun3 L g V pe (factsFrom (Control.ctlLive 1159)
    (Control.valueOf P L g w d)) factsFrom_keys c3
  obtain ⟨n2, h2⟩ := Control.eldSegST (w := w) hp d hb
  obtain ⟨n4, h4⟩ := Control.wsvSegS (L := L) (g := g) (w := w) (P := P) d
  have h2' := Seg.frameSet (H := f_ew V pe) rulesFrame (S :=
    [1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172,
      1173, 1174, 1175, 1176, 1177, 1179, 1180, 1181, 1182, 1183])
    (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) h2
  have h4' := Seg.frameSet (H := f_ew V pe) rulesFrame (S := [1179, 1180, 1181, 1182, 1183])
    (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) h4
  exact ⟨n1 + (n2 + n4), (h1.weaken_start (eld_start d hs V pe)).comp
    ((h2'.weaken_start fun _ h => holds_swap h).comp h4')⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
