-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Consumer
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Kernels.Fp16Gemm8192.Proof.Thread.Claims
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Definitions and helper facts of `ConsumerLoad`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The continuation of a step of this role: the thread leaves the role, or steps to `d'` at
`t'` by a run of `Tau` (the conclusion of each step lemma). -/
syntax "load_cont " term:max term:max term:max term:max term:max : term
macro_rules
  | `(load_cont $L $g $d $e $u) => `(next $L $g $d $e = some none ∨ ∃ d' t', next $L $g $d $e =
    some (some d') ∧
      Relation.ReflTransGen (Tau kernel [Assumptions.idealArith,
        Assumptions.clusterMbar, Assumptions.pollAgree] $L $g) $u t' ∧
      At t' d'.site.pc (facts $L $g d') ∧ Inv d')


/-- The sixteen destination registers of load `n`, in the order its instruction lists them. -/
def ldRegsN : Nat → List Nat
  | 0 => [161, 160, 163, 162, 165, 164, 167, 166,
      169, 168, 171, 170, 173, 172, 175, 174]
  | 1 => [178, 177, 180, 179, 182, 181, 184, 183,
      186, 185, 188, 187, 190, 189, 192, 191]
  | 2 => [195, 194, 197, 196, 199, 198, 201, 200,
      203, 202, 205, 204, 207, 206, 209, 208]
  | 3 => [212, 211, 214, 213, 216, 215, 218, 217,
      220, 219, 222, 221, 224, 223, 226, 225]
  | 4 => [229, 228, 231, 230, 233, 232, 235, 234,
      237, 236, 239, 238, 241, 240, 243, 242]
  | 5 => [246, 245, 248, 247, 250, 249, 252, 251,
      254, 253, 256, 255, 258, 257, 260, 259]
  | 6 => [263, 262, 265, 264, 267, 266, 269, 268,
      271, 270, 273, 272, 275, 274, 277, 276]
  | 7 => [280, 279, 282, 281, 284, 283, 286, 285,
      288, 287, 290, 289, 292, 291, 294, 293]
  | 8 => [297, 296, 299, 298, 301, 300, 303, 302,
      305, 304, 307, 306, 309, 308, 311, 310]
  | 9 => [314, 313, 316, 315, 318, 317, 320, 319,
      322, 321, 324, 323, 326, 325, 328, 327]
  | 10 => [331, 330, 333, 332, 335, 334, 337, 336,
      339, 338, 341, 340, 343, 342, 345, 344]
  | 11 => [348, 347, 350, 349, 352, 351, 354, 353,
      356, 355, 358, 357, 360, 359, 362, 361]
  | 12 => [365, 364, 367, 366, 369, 368, 371, 370,
      373, 372, 375, 374, 377, 376, 379, 378]
  | 13 => [382, 381, 384, 383, 386, 385, 388, 387,
      390, 389, 392, 391, 394, 393, 396, 395]
  | 14 => [399, 398, 401, 400, 403, 402, 405, 404,
      407, 406, 409, 408, 411, 410, 413, 412]
  | _ => [416, 415, 418, 417, 420, 419, 422, 421,
      424, 423, 426, 425, 428, 427, 430, 429]

/-- The sixteen destination registers of load `j`. -/
def ldRegs (j : Fin 16) : List Nat := ldRegsN j.val

/-- The address register of load `n`. -/
def ldAddrN : Nat → Nat
  | 0 => 159 | 1 => 176 | 2 => 193 | 3 => 210
  | 4 => 227 | 5 => 244 | 6 => 261 | 7 => 278
  | 8 => 295 | 9 => 312 | 10 => 329 | 11 => 346
  | 12 => 363 | 13 => 380 | 14 => 397
  | _ => 414

/-- The address register of load `j`. -/
def ldAddr (j : Fin 16) : Nat := ldAddrN j.val

/-- Load `j` is the Tensor Memory load at pc `749 + 10 j`, with the table's destinations. -/
theorem code_load : ∀ j : Fin 16,
    kernel.code[(Site.load j).pc]? = some ⟨none, .tcLd (ldRegs j) (ldAddr j)⟩ := by
  intro j
  fin_cases j
  · exact Flow.code_749
  · exact Flow.code_759
  · exact Flow.code_769
  · exact Flow.code_779
  · exact Flow.code_789
  · exact Flow.code_799
  · exact Flow.code_809
  · exact Flow.code_819
  · exact Flow.code_829
  · exact Flow.code_839
  · exact Flow.code_849
  · exact Flow.code_859
  · exact Flow.code_869
  · exact Flow.code_879
  · exact Flow.code_889
  · exact Flow.code_899

theorem pc_wait : ∀ j : Fin 16, (Site.loadWait j).pc = (Site.load j).pc + 1 := by
  table_decide

theorem ldRegs_len : ∀ j : Fin 16, (ldRegs j).length = 16 := by
  table_decide

theorem ldRegs_nodup : ∀ j : Fin 16, (ldRegs j).Nodup := by
  table_decide

/-- Registers outside the listed ones keep their values through a register write. -/
theorem setRegs_other (t : TState) (ds : List Nat) (vs : List Value) (r : Nat)
    (hr : r ∉ ds) : (setRegs t ds vs).regs r = t.regs r := by
  induction ds generalizing t vs with
  | nil => rfl
  | cons d ds ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      rw [setRegs, ih _ _ (by intro h; exact hr (List.mem_cons_of_mem _ h))]
      exact Function.update_of_ne (by intro h; exact hr (by simp [h])) _ _

/-- A listed register holds the value at its position, when the registers are distinct. -/
theorem setRegs_get : ∀ (ds : List Nat) (vs : List Value) (t : TState) (p : Nat) (r : Nat)
    (v : Value), ds.Nodup → ds[p]? = some r → vs[p]? = some v →
      (setRegs t ds vs).regs r = some v
  | [], _, _, _, _, _, _, hr, _ => by simp at hr
  | _ :: _, [], _, _, _, _, _, _, hv => by simp at hv
  | d :: ds, v' :: vs, t, 0, r, v, hnd, hr, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hv
    rw [← hr, ← hv]
    show (setRegs (setReg t d v') ds vs).regs d = some v'
    rw [setRegs_other (setReg t d v') ds vs d (List.nodup_cons.mp hnd).1]
    simp [setReg]
  | d :: ds, v' :: vs, t, p + 1, r, v, hnd, hr, hv => by
    simp only [List.getElem?_cons_succ] at hr hv
    exact setRegs_get ds vs (setReg t d v') p r v (List.nodup_cons.mp hnd).2 hr hv

/-- A register write keeps the thread's pc, sub-step, accumulator and fault. -/
theorem setRegs_skel : ∀ (ds : List Nat) (vs : List Value) (t : TState),
    (setRegs t ds vs).pc = t.pc ∧ (setRegs t ds vs).sub = t.sub ∧
      (setRegs t ds vs).acc = t.acc ∧ (setRegs t ds vs).fault = t.fault
  | [], _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | _ :: _, [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | d :: ds, v :: vs, t => setRegs_skel ds vs (setReg t d v)

/-- The state after the register writes of a load, at a pc with its facts. -/
theorem at_setRegs (t : TState) (ds : List Nat) (vs : List Value) {pc : Nat}
    {F : List (Nat × Value)} (hpc : t.pc = pc) (hsub : t.sub = 0) (hacc : t.acc = [])
    (hf : t.fault = none) (hF : Holds (setRegs t ds vs).regs F) :
    At (setRegs t ds vs) pc F := by
  obtain ⟨k1, k2, k3, k4⟩ := setRegs_skel ds vs t
  exact ⟨k1.trans hpc, k2.trans hsub, k3.trans hacc, k4.trans hf, hF⟩

/-- The registers a load writes hold its values: the facts of its destinations, when each
destination's value in the table is the loaded value at its position. -/
theorem holds_setRegs (t : TState) (ds : List Nat) (xs : List Value) (val : Nat → Value)
    (hnd : ds.Nodup) (hlen : xs.length = ds.length)
    (hval : ∀ p < ds.length, val (ds.getD p 0) = xs.getD p (b32 0)) :
    Holds (setRegs t ds xs).regs (Flow.factsFrom ds val) := by
  refine holds_of_pointwise fun r hr => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hr
  have hpx : p < xs.length := by omega
  have hd : ds.getD p 0 = ds[p] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  have hv := hval p hp
  rw [hd] at hv
  rw [hv]
  exact setRegs_get ds _ t p _ _ hnd (List.getElem?_eq_getElem hp)
    (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpx])

/-- The register of a fact, read from the state that holds it. -/
theorem reg_val_at {L : Launch} {g pc : Nat} {d : D} {t : TState} {r : Nat}
    (h : At t pc (factsAt L g pc d)) (hl : r ∈ Flow.live pc) :
    t.regs r = some (valueOf L g d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
