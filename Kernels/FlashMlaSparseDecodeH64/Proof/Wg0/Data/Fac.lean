-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RulesFrame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EldStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Epi.StepsHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiFacts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup
public import Lemmas.Flow.ReachFrame
public import Tactics.KernelRfl
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018

@[expose] public section

/-! # The factor word (pcs 1188-1201)

After the fence the row sum is tested (pc 1189, `%p120`): a zero sum gives the factor `0`, else
`1 / (sum + 2^(sink - maximum))` (pcs 1192-1196, `e6`); the sides meet at pc 1197 (the join), where
the descriptor address and the staging test (control) precede the pair move (pcs 1199-1200, `e7`)
that forms `%rd588`, the factor twice. The test's predicate is a data value: it is named by
generalizing its outcome and splitting. -/

/-! # The row-sum read and the row guard

After the peer's row-sum word (pc 1157) the final sum (`%r24`, pc 1158) is formed, then the head
test (pc 1161) goes either to the LSE computation (`e4`, pcs 1162-1166) and its store (pc 1178) or
over them to the store's successor (the poll, pc 1184). The branch's side is the control step's
(`afterEld`), so the step's reach is given the control facts: `ds_1157`. -/

/-! # The row guard's control stretch (pcs 1159-1161)

After the row-sum read the code loads the head bound (`ld.param`, pc 1159), compares (pc 1160,
`%p118`) and branches (pc 1161): to the LSE computation (pc 1162) when the row is inside, else
over it to the store's successor (pc 1179). The stretch holds under `Pre` (the bound is the
parameter word `64`); both sides end with no control fact. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The row is inside the heads: the stretch falls through to pc 1162. -/
theorem eldSegF (hp : Pre P L m) (d : D) (h : scmp .ge .s (r5W L g) (pw 64) = false) :
    SegU kernel Assumptions.all L g 1159 (vF P L g w 1159 d) 1162 [] := by
  w0_ldp 1159 Flow.code_1159 8 64 4 d
  w0_br 1161 Flow.code_1161 118 (scmp .ge .s (r5W L g) (pw 64)) h d
  w0_seg

/-- The row is beyond the heads: the stretch jumps to pc 1179. -/
theorem eldSegT (hp : Pre P L m) (d : D) (h : scmp .ge .s (r5W L g) (pw 64) = true) :
    SegU kernel Assumptions.all L g 1159 (vF P L g w 1159 d) 1179 [] := by
  w0_ldp 1159 Flow.code_1159 8 64 4 d
  w0_br 1161 Flow.code_1161 118 (scmp .ge .s (r5W L g) (pw 64)) h d
  w0_seg

/-- The grid-dependency instruction (pc 1188) keeps the facts. -/
theorem gridSeg : SegU kernel Assumptions.all L g 1188 [] 1189 [] := by
  w0_seg

/-- The descriptor address (pc 1197, under `Pre`) and the staging test (pc 1198), up to the pair
move (pc 1199), from the control facts of the zero-sum test. -/
theorem facSeg (hp : Pre P L m) (d : D) :
    SegU kernel Assumptions.all L g 1197 (vF P L g w 1191 d) 1199 [] := by
  refine SegU.comp (SegU.of_seg (n := 1) (fun t ht => ⟨_, run_paramAdd (pc := 1197) (k := 512)
    Flow.code_1197 ht (by decide) (holds_mem (atHolds ht) (mem_factsFrom_eq
      (by decide +kernel) rfl)) hp.param1Object (by decide),
    At.set ht (fresh_live (by decide +kernel))⟩)) ?_
  w0_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- The LSE word's run (pcs 1162-1166), then the stretch to the store (pc 1178). -/
theorem reach_lseRun (L : Launch) (g : Nat) (V : Nat → Value) (pe : Value) :
    Reach kernel Assumptions.all L g 1162 (f_ew V pe) (f_lse V pe) := by
  let W := lookupD (f_ew V pe)
  refine Reach.weaken_start (F := Gen.e4_facts0 W ++ f_ew V pe)
    (SegD.reach_then (SegD.frame (H := f_ew V pe) rulesFrame (Gen.e4_run L g W) rfl
      (by kernel_rfl) (by kernel_rfl) fun _ _ => w0SegFree _) ?_)
    fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live := [481, 482]) h (by kernel_rfl), h⟩
  exact reach_frameSet rulesFrame (S :=
      [1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177])
    (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) fun _ h => h

/-- The final sum (pc 1158) and the head test: the facts of the sum, then the side's reach. -/
theorem reach_sum (hp : Pre P L m) (d : Control.D) (V : Nat → Value) (pe : Value) (pick : Bool)
    (hb : scmp .ge .s (Control.r5W L g) (pw 64) = pick)
    (tail : Reach kernel Assumptions.all L g (if pick then 1179 else 1162) (f_ew V pe)
      (if pick then f_ew V pe else f_lse V pe)) :
    Reach kernel Assumptions.all L g 1158
      ((f_exit V ++ [1728].zip [pe]) ++ Control.vF P L g w 1159 d)
      (if pick then f_ew V pe else f_lse V pe) := by
  let W := f_ex1 V pe
  let C := Control.vF P L g w 1159 d
  let X : List (Nat × Value) := [(481, W 481), (2880, W 2880)]
  have hseg : SegU kernel Assumptions.all L g 1159 C (if pick then 1179 else 1162) [] := by
    cases pick
    · exact Control.eldSegF hp d hb
    · exact Control.eldSegT hp d hb
  refine Reach.weaken_start (F := Gen.e3_facts0 W ++ (X ++ C))
    (SegD.reach_then (SegD.frame (H := X ++ C) rulesFrame (Gen.e3_run L g W) rfl
      (by kernel_rfl) (by kernel_rfl) fun _ _ => w0SegFree _) ?_) ?_
  · refine Reach.weaken_start (F := C ++ f_ew V pe)
      (SegU.reach_then (SegU.frameSet rulesFrame (S :=
        [1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172,
          1173, 1174, 1175, 1176, 1177, 1179, 1180, 1181, 1182, 1183]) hseg
        (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl)) tail)
      fun _ h => holds_rot (A := Gen.e3_facts1 W) (B := X) h
  · intro _ h
    obtain ⟨hD, hC⟩ := (holds_append _ _ _).mp h
    exact (holds_append _ _ _).mpr ⟨holds_lookupD (live := [1727, 1728]) (by simpa using hD)
      (by kernel_rfl), (holds_append _ _ _).mpr ⟨holds_lookupD (live := [481, 2880])
        (by simpa using hD) (by kernel_rfl), hC⟩⟩

/-- **The row-sum read** (pc 1157): the final sum, then the side the head test takes. -/
theorem ds_1157 (hp : Pre P L m) {d : D} (hs : d.c.site = .eld) :
    DataStep (code P L g w) (dF L) d := by
  refine ds_ld1x hs (by nofun) Flow.code_1157 rfl rfl rfl rfl rfl rfl 1159
    (by decide +kernel) (by decide +kernel) (by intro h; cases h) (hoff_of (by kernel_rfl))
    fun x bs c' hc' _ => ?_
  have hrec : record d.c ⟨Site.eld.pc, .rd x bs⟩ d.b = { d.b with pe := loadVal bs } := by
    unfold record; rw [hs]
  have hc'' : c' = Control.afterEld L g d.c := by
    simp only [Control.succ, hs, Control.dataRd] at hc'
    exact (Option.some.inj (Option.some.inj hc')).symm
  subst hc''
  rw [hrec]
  cases hb : scmp .ge .s (Control.r5W L g) (pw 64)
  · have := reach_sum (w := w) hp d.c (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))
      (loadVal bs) false hb (reach_lseRun L g _ _)
    simpa [Control.afterEld, hb, wF, wcls, wFc, wFe, Site.pc] using this
  · have := reach_sum (w := w) hp d.c (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))
      (loadVal bs) true hb (reach_frameSet rulesFrame (S := [1179, 1180, 1181, 1182, 1183])
        (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) fun _ h => h)
    simpa [Control.afterEld, hb, wF, wcls, wFc, wFe, Site.pc] using this

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- From the join (pc 1197) to the first output load: the factor pair. -/
theorem reach_join_fac (hp : Pre P L m) (d : Control.D) (V : Nat → Value) (pe K : Value) :
    Reach kernel Assumptions.all L g 1197
      ((2956, K) :: f_ew V pe ++ Control.vF P L g w 1191 d)
      (Gen.e7_facts1 (lookupD [(2956, K)])) := by
  let C := Control.vF P L g w 1191 d
  refine Reach.weaken_start (F := C ++ ((2956, K) :: f_ew V pe))
    (SegU.reach_then (SegU.frameSet rulesFrame (S := [1197, 1198, 1199, 1200])
      (Control.facSeg hp d) (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl)) ?_)
    fun _ h => ?_
  · show Reach kernel Assumptions.all L g 1199 ((2956, K) :: f_ew V pe) _
    refine Reach.weaken_start (F := Gen.e7_facts0 (lookupD [(2956, K)]))
      (SegD.reach (Gen.e7_run L g (lookupD [(2956, K)])) Flow.code_1201 trivial rfl
        fun _ _ h => h) fun _ h => ⟨h.1, trivial⟩
  · obtain ⟨hD, hC⟩ := (holds_append _ _ _).mp h
    exact (holds_append _ _ _).mpr ⟨hC, hD⟩

/-- From the fence's end (pc 1188) to the first output load: the zero-sum test, its two sides and
the join. -/
theorem reach_fac (hp : Pre P L m) (d : Control.D) (V : Nat → Value) (pe : Value) :
    Reach kernel Assumptions.all L g 1188 (f_ew V pe ++ Control.vF P L g w 1191 d)
      (f_fac V pe) := by
  let W := lookupD (f_ew V pe)
  let C := Control.vF P L g w 1191 d
  refine Reach.weaken_start (F := [] ++ (f_ew V pe ++ C))
    (SegU.reach_then (SegU.frameSet rulesFrame (S :=
      [1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200])
      Control.gridSeg (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl)) ?_)
    fun _ h => (holds_append _ _ _).mpr ⟨trivial, h⟩
  show Reach kernel Assumptions.all L g 1189 (f_ew V pe ++ C) (f_fac V pe)
  refine Reach.weaken_start (F := Gen.e5_facts0 W ++ (f_ew V pe ++ C))
    (SegD.reach_then (SegD.frame (H := f_ew V pe ++ C) rulesFrame (Gen.e5_run L g W) rfl
      (by kernel_rfl) (by kernel_rfl) fun _ _ => w0SegFree _) ?_)
    fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live := [482])
      ((holds_append _ _ _).mp h).1 (by kernel_rfl), h⟩
  show Reach kernel Assumptions.all L g 1191 (Gen.e5_facts1 W ++ (f_ew V pe ++ C)) (f_fac V pe)
  obtain ⟨q, hq⟩ : ∃ q, Gen.e5_v1189 W = .pred q := ⟨_, rfl⟩
  have hz : f_zj V pe = if q then Gen.e5_v1190 W else Gen.e6_v1196 W := by
    unfold f_zj; rw [hq]; rfl
  have hf : f_fac V pe = Gen.e7_facts1 (lookupD [(2956, if q then Gen.e5_v1190 W else
      Gen.e6_v1196 W)]) := by
    unfold f_fac; rw [hz]
  have h5 : Gen.e5_facts1 W = [(120, .pred q), (2956, Gen.e5_v1190 W)] := by
    unfold Gen.e5_facts1; rw [hq]
  rw [hf, h5]
  cases q
  · refine SegU.reach_then (SegU.branch false Flow.code_1191 bra_rule noSegments.segFreePc) ?_
    refine Reach.weaken_start (F := Gen.e6_facts0 W ++ (f_ew V pe ++ C))
      (SegD.reach_then (SegD.frame (H := f_ew V pe ++ C) rulesFrame (Gen.e6_run L g W) rfl
        (by kernel_rfl) (by kernel_rfl) fun _ _ => w0SegFree _) ?_)
      fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live := [481, 482, 2880])
        ((holds_append _ (f_ew V pe) C).mp h.2).1 (by kernel_rfl), h.2⟩
    refine Reach.weaken_start (reach_join_fac (w := w) hp d V pe (Gen.e6_v1196 W)) fun _ h => ?_
    obtain ⟨h6, hr⟩ := (holds_append _ _ _).mp h
    obtain ⟨-, -, -, -, h2956, -⟩ := h6
    exact ⟨h2956, hr⟩
  · refine SegU.reach_then (SegU.branch true Flow.code_1191 bra_rule noSegments.segFreePc) ?_
    exact Reach.weaken_start (reach_join_fac (w := w) hp d V pe (Gen.e5_v1190 W)) fun _ h => h

/-- **The fence before the zero-sum test** (pc 1187): the factor word at the first output load. -/
theorem ds_1187 (hp : Pre P L m) {d : D} (hs : d.c.site = .efa) :
    DataStep (code P L g w) (dF L) d :=
  ds_nxc (s' := .old 0) hs (by nofun) Flow.code_1187
    (fun _ _ _ hf => Code.fires_tcPlain_next (.inl rfl) hf) rfl
    (fun c' h => congrArg wcls (by simpa [succOk, hs] using h)) (by intro h; cases h) 1191
    (by decide +kernel) fun e => by
  have hr : record d.c e d.b = d.b := by unfold record; rw [hs]
  rw [hr]
  exact reach_fac (g := g) (w := w) hp d.c (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))
    d.b.pe

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
