-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.Base
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Flow.LdConsumed

@[expose] public section

/-! # The Tensor Memory loads and stores of the correction warps

The obligations of the role's Tensor Memory instructions, which `site_cases` does not cover:

* a rescale load (a site of the `tcLdDataflow` assumption) at sub-step 0 writes its sixteen
  destinations and stays at the instruction at sub-step 1 (`corr_rld`, by `step_tcLdLoad`); its
  implicit wait continues at the next instruction (`corr_rldw`, by `step_tcLdWait`);
* a final-stage load writes its eight destinations and continues (`corr_fld`, by `step_tcLd`);
* a Tensor Memory store continues at the next instruction (`corr_tst`, by `step_issueAt` and
  `fires_tcSt_next`: no assumption selects these stores with `tcStWaitLd`).

The facts after a load are the table's at the load's next instruction (`holds_setRegs_live`):
each destination holds the real number the machine recorded (`flN_get`), and every other live
register is outside the chunk's data registers, where the tables of the states before and after
the load agree (`valueOf_rldw`, `valueOf_fwl`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The loaded elements the machine recorded are the loaded values. -/
theorem flN_get {n : Nat} {vals : List Value} {xs : Nat → ℝ} (h : flN n vals = some xs)
    {i : Nat} (hi : i < n) (dflt : Value) : vals.getD i dflt = fv (xs i) := by
  unfold flN at h
  split at h
  · rename_i hall
    obtain rfl := Option.some.inj h
    have hs := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
    show vals.getD i dflt = fv ((fl32 (vals.getD i (.pred false))).getD 0)
    cases hv : vals[i]? with
    | none => simp [List.getD_eq_getElem?_getD, hv, fl32] at hs
    | some w =>
      simp only [List.getD_eq_getElem?_getD, hv, Option.getD_some] at hs ⊢
      revert hs
      cases w with
      | float f x => cases f <;> simp [fl32]
      | _ => simp [fl32]
  · cases h

/-- A key outside a list's first part is looked up in its second part. -/
theorem lookup_append_out {l1 l2 : List (Nat × Value)} {r : Nat} (h : ∀ q ∈ l1, q.1 ≠ r) :
    (l1 ++ l2).lookup r = l2.lookup r := by
  induction l1 with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨a, b⟩ := q
    have ha : a ≠ r := h _ (List.mem_cons_self ..)
    simp only [List.cons_append, List.lookup, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have : (r == a) = false := by simp; omega
    rw [this]

theorem rLoaded_keys {st : Fin 2} {c : Fin 8} {xs : Nat → ℝ} {r : Nat}
    (h : r < rBase st c ∨ rBase st c + 32 ≤ r) : ∀ q ∈ rLoaded st c xs, q.1 ≠ r := by
  intro q hq
  simp only [rLoaded, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  simp only
  omega

theorem rProducts_keys {st : Fin 2} {c : Fin 8} {xs : Nat → ℝ} {s : ℝ} {r : Nat}
    (h : r < rBase st c ∨ rBase st c + 32 ≤ r) : ∀ q ∈ rProducts st c xs s, q.1 ≠ r := by
  intro q hq
  simp only [rProducts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  obtain ⟨i, hi, rfl | rfl⟩ := hq <;> simp only <;> omega

/-- Outside a rescale chunk's data registers the table at its load's wait is the load's. -/
theorem valueOf_rldw {p : Params} {L : Launch} {g : Nat} {st : Fin 2} {c : Fin 8} {v : V}
    {X : Nat → ℝ} {k k' : Fin 4} {r : Nat} (h : r < rBase st c ∨ rBase st c + 32 ≤ r) :
    valueOf p L g ⟨.rldw st c, { v with xs := X }, k⟩ r = valueOf p L g ⟨.rld st c, v, k'⟩ r := by
  simp only [valueOf, values, List.append_assoc]
  rw [lookup_append_out (rLoaded_keys h), lookup_append_out (rProducts_keys h),
    lookup_append_out (rLoaded_keys h), lookup_append_out (rProducts_keys h)]
  rfl

theorem fChunk_keys {st : Fin 2} {j : Fin 16} {ys : Nat → ℝ} {x : ℝ} {r : Nat}
    (h : (r < fBase st j ∨ fBase st j + 17 ≤ r) ∧ (r < fPack st j ∨ fPack st j + 8 ≤ r)) :
    ∀ q ∈ fChunk st j ys x, q.1 ≠ r := by
  intro q hq
  simp only [fChunk, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with ⟨i, hi, rfl⟩ | hq
  · simp only; omega
  · split at hq <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp only <;> omega

/-- Outside a final chunk's data registers the table at its load's wait is the load's. -/
theorem valueOf_fwl {p : Params} {L : Launch} {g : Nat} {st : Fin 2} {j : Fin 16} {v : V}
    {Y : Nat → ℝ} {r : Nat}
    (h : (r < fBase st j ∨ fBase st j + 17 ≤ r) ∧ (r < fPack st j ∨ fPack st j + 8 ≤ r)) :
    valueOf p L g ⟨.fwl st j, { v with ys := Y }, 0⟩ r = valueOf p L g ⟨.fld st j, v, 0⟩ r := by
  simp only [valueOf, values, List.append_assoc]
  rw [lookup_append_out (fChunk_keys h), lookup_append_out (fChunk_keys h)]
  rfl

/-- The registers of a rescale load's next instruction, from a checked list fact: each is a
destination, or live before the load and outside the chunk's data registers, where the two
tables agree. -/
theorem rld_other {p : Params} {L : Launch} {g : Nat} {st : Fin 2} {c : Fin 8} {v : V}
    {X : Nat → ℝ} {ds live live' : List Nat}
    (h : live'.all (fun r => ds.contains r || (live.contains r &&
      (decide (r < rBase st c) || decide (rBase st c + 32 ≤ r)))) = true) :
    ∀ r ∈ live', r ∉ ds → r ∈ live ∧
      valueOf p L g ⟨.rldw st c, { v with xs := X }, 1⟩ r = valueOf p L g ⟨.rld st c, v, 0⟩ r := by
  intro r hr hd
  have := List.all_eq_true.mp h r hr
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at this
  rcases this with h1 | ⟨h2, h3⟩
  · exact absurd h1 hd
  · exact ⟨h2, valueOf_rldw h3⟩

/-- The registers of a final load's next instruction, as `rld_other`. -/
theorem fld_other {p : Params} {L : Launch} {g : Nat} {st : Fin 2} {j : Fin 16} {v : V}
    {Y : Nat → ℝ} {ds live live' : List Nat}
    (h : live'.all (fun r => ds.contains r || (live.contains r &&
      ((decide (r < fBase st j) || decide (fBase st j + 17 ≤ r)) &&
       (decide (r < fPack st j) || decide (fPack st j + 8 ≤ r))))) = true) :
    ∀ r ∈ live', r ∉ ds → r ∈ live ∧
      valueOf p L g ⟨.fwl st j, { v with ys := Y }, 0⟩ r = valueOf p L g ⟨.fld st j, v, 0⟩ r := by
  intro r hr hd
  have := List.all_eq_true.mp h r hr
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at this
  rcases this with h1 | ⟨h2, h3⟩
  · exact absurd h1 hd
  · exact ⟨h2, valueOf_fwl h3⟩

theorem b32_toNat (x : BitVec 64) : Value.bits 32 x = b32 x.toNat := by
  simp [b32]

theorem truncBits_lt (x : BitVec 64) : (truncBits 32 x).toNat < 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

/-- The first `q` keys of a run `b, b + 1, …` are looked up at their values. -/
theorem lookup_run {b n q : Nat} (F : Nat → Value) (l : List (Nat × Value)) (hq : q < n) :
    ((List.range n).map (fun i => (b + i, F i)) ++ l).lookup (b + q) = some (F q) := by
  induction n generalizing l with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.append_assoc]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
    · exact ih _ h
    · have hout : ∀ x ∈ (List.range q).map (fun i => (b + i, F i)), x.1 ≠ b + q := by
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simp only
        omega
      rw [lookup_append_out hout]
      simp

/-- A rescale load at sub-step 0: the load writes the sixteen elements of the chunk, which the
machine records, and the thread stays at the instruction for its implicit wait. -/
theorem rld_ok {p : Params} {L : Launch} {g : Nat} {st : Fin 2} {c : Fin 8} {v : V}
    {gd : Option (Nat × Bool)} {ds : List Nat} {ta : Nat} {sh : TcShape} {a0 : Nat}
    (hc : kernel.code[rldPc st c]? = some ⟨gd, .tcLd ds ta sh none⟩)
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : Assumptions.all.any (·.tcLdWait (rldPc st c)) = true)
    (hta : (ta, b32 a0) ∈ facts p L g ⟨.rld st c, v, 0⟩) (ha0 : a0 < 2 ^ 32)
    (hds : ds = (List.range 16).map (rBase st c + ·))
    (hlive : (Flow.live (rldPc st c + 1)).all (fun r => ds.contains r ||
      ((Flow.live (rldPc st c)).contains r &&
        (decide (r < rBase st c) || decide (rBase st c + 32 ≤ r)))) = true) :
    (code p L g).StepOk ⟨.rld st c, v, 0⟩ := by
  refine PTX.Flow.Code.step_tcLdLoad
    (nv := fun vals => match flN 16 vals with
      | some xs => some (some (⟨.rldw st c, { v with xs := xs }, 1⟩ : D))
      | none => some none) hc hsh hw hta ha0 (fun _ _ => rfl) rfl rfl
    (fun vals => by cases flN 16 vals <;> simp) ?_
  intro vals d' hv
  cases hf : flN 16 vals with
  | none => simp [hf] at hv
  | some xs =>
    simp only [hf, Option.some.injEq] at hv
    subst hv
    refine ⟨rfl, rfl, rfl, fun _ => Or.inr rfl, fun hlen t hF => ?_⟩
    subst hds
    refine PTX.Flow.holds_setRegs_live hF ?_ hlen ?_ (rld_other hlive)
    · exact (List.nodup_range).map (fun _ _ h => by omega)
    · intro q hq
      simp only [List.length_map, List.length_range] at hq
      rw [flN_get hf hq]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
        Option.map_some, Option.getD_some]
      show ((rLoaded st c xs ++ _).lookup (rBase st c + q)).getD _ = _
      rw [rLoaded, lookup_run _ _ hq]
      rfl

theorem ori_lt (x : BitVec 64) (n : Int) : (Mma.ori x n).toNat < 2 ^ 32 := by
  simp only [Mma.ori, Epilogue.r32, Epilogue.i32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat]
  exact Nat.or_lt_two_pow (by omega) (by omega)

/-- The code from position 7744 (the correction warps' code starts at 7746) as the decoder's
chunks: one evaluation of the drop, so that the tensor-load condition of a correction site walks
only this slice (`tcLdWait_at`). -/
def corrCode : List Instr :=
    Decoded.code242 ++ (Decoded.code243 ++ (Decoded.code244 ++ (Decoded.code245 ++
    (Decoded.code246 ++ (Decoded.code247 ++ (Decoded.code248 ++ (Decoded.code249 ++
    (Decoded.code250 ++ (Decoded.code251 ++ (Decoded.code252 ++ (Decoded.code253 ++
    (Decoded.code254 ++ (Decoded.code255 ++ (Decoded.code256 ++ (Decoded.code257 ++
    (Decoded.code258 ++ (Decoded.code259 ++ (Decoded.code260 ++ (Decoded.code261 ++
    (Decoded.code262 ++ (Decoded.code263 ++ (Decoded.code264 ++ (Decoded.code265 ++
    (Decoded.code266 ++ (Decoded.code267 ++ (Decoded.code268 ++ (Decoded.code269 ++
    (Decoded.code270 ++ (Decoded.code271 ++ (Decoded.code272 ++ (Decoded.code273 ++
    (Decoded.code274 ++ (Decoded.code275 ++ (Decoded.code276 ++ (Decoded.code277 ++
    (Decoded.code278 ++ (Decoded.code279 ++ (Decoded.code280 ++ (Decoded.code281 ++
    (Decoded.code282 ++ (Decoded.code283 ++ (Decoded.code284 ++ (Decoded.code285 ++
    (Decoded.code286 ++ (Decoded.code287)))))))))))))))))))))))))))))))))))))))))))))

theorem corr_tail : kernel.code.drop 7744 = corrCode := by
  kernel_rfl

/-- **The implicit `wait::ld` of a correction load, on the slice**: `Assumptions.all_tcLdWait` with
`ldConsumedAt` read from `corr_tail` (`Flow.ldConsumedAt_eq_in`), so that the kernel does not walk
the code from its head at every site. -/
theorem tcLdWait_at {pc : Nat} (h : 7744 ≤ pc) :
    Assumptions.all.any (·.tcLdWait pc) =
      (Assumptions.tcLdDataflowSites.contains pc && Flow.ldConsumedIn corrCode (pc - 7744)) := by
  rw [Assumptions.all_tcLdWait, Flow.ldConsumedAt_eq_in corr_tail h]

/-- The implicit `wait::ld` condition at a correction load site. -/
macro "corr_wait" : tactic => `(tactic|
  (rw [PTX.Kernels.TmlFa4Fwd.Proof2.Correction.tcLdWait_at (Nat.le_of_ble_eq_true rfl)];
    kernel_rfl))

/-- A rescale load at sub-step 0 (an override of `corr_sites`). -/
syntax "corr_rld" : tactic
macro_rules
  | `(tactic| corr_rld) => `(tactic| (
      refine' PTX.Kernels.TmlFa4Fwd.Proof2.Correction.rld_ok ?hc ?hsh ?hw ?hta ?ha0 ?hds ?hlive
      case hc => code_lookup
      case hsh => intro s hs; cases hs
      case hw => corr_wait
      case hta =>
        rw [← PTX.Kernels.TmlFa4Fwd.Proof2.Correction.b32_toNat]
        exact PTX.Flow.mem_factsFrom (by lit_mem)
      case ha0 => first
        | with_reducible exact PTX.Kernels.TmlFa4Fwd.Proof2.Correction.truncBits_lt _
        | with_reducible exact PTX.Kernels.TmlFa4Fwd.Proof2.Correction.ori_lt _ _
      case hds => rfl
      case hlive => kernel_rfl))

/-- The implicit wait of a rescale load (an override of `corr_sites`). -/
syntax "corr_rldw" : tactic
macro_rules
  | `(tactic| corr_rldw) => `(tactic| (
      refine' (PTX.Flow.Code.step_tcLdWait (dn := ?dn) ?hc ?hw ?hn rfl rfl ?hl)
      case hc => code_lookup
      case hw => corr_wait
      case hn => intro e; rfl
      case hl => lands_auto (corr_seg) (corr_inv)))

/-- A Tensor Memory store (an override of `corr_sites`). -/
syntax "corr_tst" : tactic
macro_rules
  | `(tactic| corr_tst) => `(tactic| (
      refine' (PTX.Flow.Code.step_issueAt (dn := ?dn) ?hc ?hadv ?hn rfl rfl ?hl)
      case hc => code_lookup
      case hadv =>
        intro t e u hpc hf
        exact PTX.Flow.fires_tcSt_next
          (by rw [hpc, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; rfl) hf
      case hn => intro e; rfl
      case hl => lands_auto (corr_seg) (corr_inv)))

/-- A final-stage load: it writes the eight elements of the chunk, which the machine records,
and continues at the next instruction to the chunk's wait. -/
theorem fld_ok {p : Params} {L : Launch} {g : Nat} {st : Fin 2} {j : Fin 16} {v : V}
    {gd : Option (Nat × Bool)} {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hc : kernel.code[fldPc st j]? = some ⟨gd, .tcLd ds ta sh none⟩)
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : Assumptions.all.any (·.tcLdWait (fldPc st j)) = false)
    (hds : ds = (List.range 8).map (fBase st j + ·))
    (hlive : (Flow.live (fldPc st j + 1)).all (fun r => ds.contains r ||
      ((Flow.live (fldPc st j)).contains r &&
        ((decide (r < fBase st j) || decide (fBase st j + 17 ≤ r)) &&
         (decide (r < fPack st j) || decide (fPack st j + 8 ≤ r))))) = true)
    (hl : ∀ ys : Nat → ℝ, (code p L g).Lands ⟨.fld st j, v, 0⟩ (fldPc st j + 1)
      (Flow.factsFrom (Flow.live (fldPc st j + 1))
        (valueOf p L g ⟨.fwl st j, { v with ys := ys }, 0⟩))
      ⟨.fwl st j, { v with ys := ys }, 0⟩) :
    (code p L g).StepOk ⟨.fld st j, v, 0⟩ := by
  refine PTX.Flow.Code.step_tcLd
    (nv := fun vals => match flN 8 vals with
      | some ys => some (some (⟨.fwl st j, { v with ys := ys }, 0⟩ : D))
      | none => some none)
    (F' := fun vals => match flN 8 vals with
      | some ys => Flow.factsFrom (Flow.live (fldPc st j + 1))
          (valueOf p L g ⟨.fwl st j, { v with ys := ys }, 0⟩)
      | none => []) hc hsh hw (fun _ _ => rfl) rfl rfl ?_
    (fun vals => by cases flN 8 vals <;> simp) ?_
  · intro t vals d' hv hlen hF
    cases hf : flN 8 vals with
    | none => simp [hf] at hv
    | some ys =>
      subst hds
      refine PTX.Flow.holds_setRegs_live hF ?_ hlen ?_ (fld_other hlive)
      · exact (List.nodup_range).map (fun _ _ h => by omega)
      · intro q hq
        simp only [List.length_map, List.length_range] at hq
        rw [flN_get hf hq]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
          Option.map_some, Option.getD_some]
        show ((fChunk st j ys _ ++ _).lookup (fBase st j + q)).getD _ = _
        rw [fChunk, List.append_assoc, lookup_run _ _ hq]
        rfl
  · intro vals d' hv
    cases hf : flN 8 vals with
    | none => simp [hf] at hv
    | some ys =>
      simp only [hf, Option.some.injEq] at hv
      subst hv
      exact hl ys

/-- A final-stage load (an override of `corr_sites`). -/
syntax "corr_fld" : tactic
macro_rules
  | `(tactic| corr_fld) => `(tactic| (
      refine' PTX.Kernels.TmlFa4Fwd.Proof2.Correction.fld_ok ?hc ?hsh ?hw ?hds ?hlive ?hl
      case hc => code_lookup
      case hsh => intro s hs; cases hs
      case hw => corr_wait
      case hds => rfl
      case hlive => kernel_rfl
      case hl =>
        intro ys
        lands_auto (corr_seg) (corr_inv)))

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
