-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Spec
public import Init.Data.Nat.ToString
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Lemmas.Flow.ParamObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section
set_option maxRecDepth 2000

private theorem kernelName : kernel.name =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tenso\
    r000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64div8_\
    0" := rfl

private theorem decimal1 : toString (1 : Nat) = "1" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_one.mpr rfl]
  rfl

private theorem decimal2 : toString (2 : Nat) = "2" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_two.mpr rfl]
  rfl

private theorem decimal4 : toString (4 : Nat) = "4" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_four.mpr rfl]
  rfl

private theorem decimal5 : toString (5 : Nat) = "5" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_five.mpr rfl]
  rfl

private theorem decimal6 : toString (6 : Nat) = "6" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_six.mpr rfl]
  rfl

private theorem decimal7 : toString (7 : Nat) = "7" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_seven.mpr rfl]
  rfl

private theorem decimal9 : toString (9 : Nat) = "9" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_nine.mpr rfl]
  rfl

private theorem decimal10 : toString (10 : Nat) = "10" := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
  simp only [show (10 / 10 : Nat) = 1 by decide, show (10 % 10 : Nat) = 0 by decide,
    Nat.repr_of_lt (n := 0) (by decide), Nat.repr_of_lt (n := 1) (by decide),
    Nat.digitChar_eq_zero.mpr rfl, Nat.digitChar_eq_one.mpr rfl]
  rfl

private theorem decimal11 : toString (11 : Nat) = "11" := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
  simp only [show (11 / 10 : Nat) = 1 by decide, show (11 % 10 : Nat) = 1 by decide,
    Nat.repr_of_lt (n := 1) (by decide),
    Nat.digitChar_eq_one.mpr rfl]
  rfl

private theorem decimal24 : toString (24 : Nat) = "24" := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
  simp only [show (24 / 10 : Nat) = 2 by decide, show (24 % 10 : Nat) = 4 by decide,
    Nat.repr_of_lt (n := 2) (by decide), Nat.repr_of_lt (n := 4) (by decide),
    Nat.digitChar_eq_two.mpr rfl, Nat.digitChar_eq_four.mpr rfl]
  rfl

/-- The ABI byte encoding reconstructs the supplied unsigned word. -/
private theorem paramWord {l : Launch} {name : String} : ∀ {n x off : Nat},
    x < 256 ^ n →
    (∀ k < n, l.paramBytes name (off + k) = some (leByte x k)) →
    PTX.Flow.paramNat l name off n = x
  | 0, x, _, hx, _ => by simp only [pow_zero] at hx; simp [PTX.Flow.paramNat, show x = 0 by omega]
  | n + 1, x, off, hx, h => by
    have h0 : l.paramBytes name off = some (leByte x 0) := by simpa using h 0 (by omega)
    have hx' : x / 256 < 256 ^ n := (Nat.div_lt_iff_lt_mul (by decide)).2 (by
      simpa only [pow_succ] using hx)
    have h' : ∀ k < n, l.paramBytes name (off + 1 + k) = some (leByte (x / 256) k) := by
      intro k hk
      rw [show off + 1 + k = off + (k + 1) by omega, h (k + 1) (by omega)]
      simp only [leByte, Nat.div_div_eq_div_mul, pow_succ']
    simp only [PTX.Flow.paramNat, h0, Option.getD_some, paramWord hx' h', leByte,
      pow_zero, Nat.div_one, BitVec.toNat_ofNat]
    exact Nat.mod_add_div x 256

private theorem objectWord {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    {i off bytes value : Nat} (h : (i, off, bytes, value) ∈ p.objectWords) :
    PTX.Flow.ParamSupplied l (param i) off bytes ∧ PTX.Flow.paramNat l
      (param i) off bytes = value := by
  obtain ⟨hb, hr⟩ := hpre.objectBytes i off bytes value h
  exact ⟨fun k hk => ⟨leByte value k, hr k hk⟩, paramWord hb hr⟩

private def put (t : TState) (r : Nat) (v : Value) : TState := next (setReg t r v)

private theorem runPut {l : Launch} {g pc : Nat} {t : TState} {r : Nat} {v : Value} {op : Op}
    (hpc : t.pc = pc) (hf : t.fault = none) (hc : kernel.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (he : execLocal l g t op = .ok (put t r v)) :
    run kernel [] l g 1 t = some (put t r v) := by
  have he' : execLocalA [] l g t op = .ok (put t r v) := he
  simp only [run, tauStep, out, hf, hpc, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, he']
  rfl

private def objectLoad (i off w : Nat) (ds : List Nat) : MemAccess :=
  { kind := .load, space := some .param, sem := .weak, elem := .int .b w,
    vec := ds.length, addr := ⟨.param (param i) true, (off : Int)⟩, dsts := ds.map some }

private theorem runLoad64 {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    {g pc i off d x : Nat} {t : TState} (h : (i, off, 8, x) ∈ p.objectWords)
    (hpc : t.pc = pc) (hf : t.fault = none)
    (hc : kernel.code[pc]? = some ⟨none, .mem (objectLoad i off 64 [d])⟩) :
    run kernel [] l g 1 t = some (put t d (b64 x)) := by
  obtain ⟨hbytes, hx⟩ := objectWord hpre h
  apply runPut hpc hf hc rfl
  have hLoad : (objectLoad i off 64 [d]).rule = some .threadMove := rfl
  rw [execLocal_mem hLoad]
  change next <$> loadParamObject l 64 64 (param i) t off [d] = _
  simp only [PTX.Flow.loadParamObject_eq (w := 64) (dw := 64) (ds := [d]) hbytes, Functor.map,
    Except.map, PTX.Flow.loadParamRegs, hx]
  rfl

private theorem runLoadHeads {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    {g : Nat} {t : TState} (hpc : t.pc = 4) (hf : t.fault = none) :
    run kernel [] l g 1 t = some (next (setReg (setReg t 1663 (b32 16)) 1664 (b32 p.kvHeads))) := by
  obtain ⟨h₁, hx₁⟩ := objectWord hpre (i := 1) (off := 8) (bytes := 4) (value := 16)
    (by simp [Params.objectWords])
  obtain ⟨h₂, hx₂⟩ := objectWord hpre (i := 1) (off := 12) (bytes := 4) (value := p.kvHeads)
    (by simp [Params.objectWords])
  have hLoad : PTX.Flow.ParamSupplied l (param 1) 8 8 := by
    intro k hk
    by_cases hk' : k < 4
    · exact h₁ k hk'
    · simpa only [show 12 + (k - 4) = 8 + k by omega] using h₂ (k - 4) (by omega)
  have he : execLocalA [] l g t (.mem (objectLoad 1 8 32 [1663, 1664])) =
      .ok (next (setReg (setReg t 1663 (b32 16)) 1664 (b32 p.kvHeads))) := by
    change execLocal l g t (.mem (objectLoad 1 8 32 [1663, 1664])) = _
    have hr : (objectLoad 1 8 32 [1663, 1664]).rule = some .threadMove := rfl
    rw [execLocal_mem hr]
    change next <$> loadParamObject l 32 32 (param 1) t 8 [1663, 1664] = _
    simp only [PTX.Flow.loadParamObject_eq (w := 32) (dw := 32) (ds := [1663, 1664]) hLoad,
      Functor.map, Except.map,
      PTX.Flow.loadParamRegs, show (32 / 8 : Nat) = 4 by decide, show (8 + 4 : Nat) = 12 by decide,
      hx₁, hx₂]
    rfl
  have hc : kernel.code[4]? = some ⟨none, .mem (objectLoad 1 8 32 [1663, 1664])⟩ := by
    rw [Flow.code_4]
    simp only [objectLoad, param, kernelName, decimal1]
    rfl
  simp only [run, tauStep, out, hf, hpc, hc, guardHolds, pure, Except.pure,
    show (Op.mem (objectLoad 1 8 32 [1663, 1664])).isLocal = true from rfl, ↓reduceIte, he]
  rfl

private theorem runParamPtr {l : Launch} {g pc i d : Nat} {t : TState}
    (hpc : t.pc = pc) (hf : t.fault = none)
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.scalar, .int .b 64, [some d],
          [.paramSym (param i)]⟩⟩) :
    run kernel [] l g 1 t = some (put t d (.ptr 64 false (.param (param i)) 0)) := by
  apply runPut hpc hf hc rfl
  rw [execLocal_move rfl]
  simp [execMove, DType.width, readValue, pure, Except.pure, bind, Except.bind, Value.bytes, put]

private theorem trunc64 (x : BitVec 64) : truncBits 64 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp [truncBits, Nat.mod_eq_of_lt x.isLt]

private theorem runLocalAdd {l : Launch} {g pc d k : Nat} {t : TState}
    (hpc : t.pc = pc) (hf : t.fault = none) (hb : t.regs 1 = some (b64 l.localBase))
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .u 64, false, [some d], [.reg 1, .imm
            k]⟩⟩) :
    run kernel [] l g 1 t = some (put t d (b64 (l.localBase + k))) := by
  apply runPut hpc hf hc rfl
  rw [execLocal_int rfl]
  simp only [execInt, DType.width, readValue, readBits, readReg, hb, bind, Except.bind,
    pure, Except.pure, b64, trunc64, BitVec.ofInt_natCast]
  change (Except.ok (put t d (.bits 64 (BitVec.ofNat 64 l.localBase + BitVec.ofNat 64 k))) : Exec
    TState) = _
  rw [← BitVec.ofNat_add]

/-- Parameter words and address registers live at the first shuffle. -/
def abiFacts (p : Params) (l : Launch) : List (Nat × Value) :=
  [(1, b64 l.localBase),
   (7492, b64 p.kLayout.base), (7493, b64 p.kLayout.rowStride),
   (7494, b64 p.kLayout.headStride), (7495, b64 p.kLayout.pageStride),
   (1663, b32 16), (1664, b32 p.kvHeads),
   (7496, b64 p.vLayout.base), (7497, b64 p.vLayout.rowStride),
   (7498, b64 p.vLayout.headStride), (7499, b64 p.vLayout.pageStride),
   (7500, b64 p.lseBase), (7501, b64 p.lseStride),
   (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
   (7504, b64 p.pageTableBase), (7505, b64 p.pageTableStride),
   (7291, .ptr 64 false (.param (param 9)) 0),
   (7290, .ptr 64 false (.param (param 10)) 0),
   (7289, .ptr 64 false (.param (param 11)) 0),
   (7506, b64 p.cuQBase),
   (7292, b64 (l.localBase + 0)), (7293, b64 (l.localBase + 32)),
   (7294, b64 (l.localBase + 64)), (7295, b64 (l.localBase + 96)),
   (1665, b32 l.sharedBase)]

/-- The complete local prefix reads all ABI arguments and reaches the shared-base broadcast. -/
theorem startWith {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m) (g : Nat) :
    ∃ t, run kernel A l g 25 {} = some t ∧ At t 25 (abiFacts p l) := by
  let t0 : TState := {}
  let t1 := put t0 1 (b64 l.localBase)
  have h1 : run kernel [] l g 1 t0 = some t1 := by
    apply runPut rfl rfl Flow.code_0 rfl
    rw [execLocal_move rfl]
    rfl
  let t2 := put t1 7495 (b64 p.kLayout.pageStride)
  have h2 : run kernel [] l g 1 t1 = some t2 :=
    runLoad64 hpre (i := 1) (off := 40) (pc := 1) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_1]
      simp only [objectLoad, param, kernelName, decimal1]
      rfl)
  let t3 := put t2 7494 (b64 p.kLayout.headStride)
  have h3 : run kernel [] l g 1 t2 = some t3 :=
    runLoad64 hpre (i := 1) (off := 32) (pc := 2) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_2]
      simp only [objectLoad, param, kernelName, decimal1]
      rfl)
  let t4 := put t3 7493 (b64 p.kLayout.rowStride)
  have h4 : run kernel [] l g 1 t3 = some t4 :=
    runLoad64 hpre (i := 1) (off := 24) (pc := 3) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_3]
      simp only [objectLoad, param, kernelName, decimal1]
      rfl)
  let t5 := next (setReg (setReg t4 1663 (b32 16)) 1664 (b32 p.kvHeads))
  have h5 : run kernel [] l g 1 t4 = some t5 := runLoadHeads hpre rfl rfl
  let t6 := put t5 7492 (b64 p.kLayout.base)
  have h6 : run kernel [] l g 1 t5 = some t6 :=
    runLoad64 hpre (i := 1) (off := 0) (pc := 5) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_5]
      simp only [objectLoad, param, kernelName, decimal1]
      rfl)
  let t7 := put t6 7499 (b64 p.vLayout.pageStride)
  have h7 : run kernel [] l g 1 t6 = some t7 :=
    runLoad64 hpre (i := 2) (off := 40) (pc := 6) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_6]
      simp only [objectLoad, param, kernelName, decimal2]
      rfl)
  let t8 := put t7 7498 (b64 p.vLayout.headStride)
  have h8 : run kernel [] l g 1 t7 = some t8 :=
    runLoad64 hpre (i := 2) (off := 32) (pc := 7) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_7]
      simp only [objectLoad, param, kernelName, decimal2]
      rfl)
  let t9 := put t8 7497 (b64 p.vLayout.rowStride)
  have h9 : run kernel [] l g 1 t8 = some t9 :=
    runLoad64 hpre (i := 2) (off := 24) (pc := 8) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_8]
      simp only [objectLoad, param, kernelName, decimal2]
      rfl)
  let t10 := put t9 7496 (b64 p.vLayout.base)
  have h10 : run kernel [] l g 1 t9 = some t10 :=
    runLoad64 hpre (i := 2) (off := 0) (pc := 9) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_9]
      simp only [objectLoad, param, kernelName, decimal2]
      rfl)
  let t11 := put t10 7501 (b64 p.lseStride)
  have h11 : run kernel [] l g 1 t10 = some t11 :=
    runLoad64 hpre (i := 4) (off := 16) (pc := 10) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_10]
      simp only [objectLoad, param, kernelName, decimal4]
      rfl)
  let t12 := put t11 7500 (b64 p.lseBase)
  have h12 : run kernel [] l g 1 t11 = some t12 :=
    runLoad64 hpre (i := 4) (off := 0) (pc := 11) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_11]
      simp only [objectLoad, param, kernelName, decimal4]
      rfl)
  let t13 := put t12 7502 (b64 p.cuQBase)
  have h13 : run kernel [] l g 1 t12 = some t13 :=
    runLoad64 hpre (i := 5) (off := 0) (pc := 12) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_12]
      simp only [objectLoad, param, kernelName, decimal5]
      rfl)
  let t14 := put t13 7503 (b64 p.usedKBase)
  have h14 : run kernel [] l g 1 t13 = some t14 :=
    runLoad64 hpre (i := 6) (off := 0) (pc := 13) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_13]
      simp only [objectLoad, param, kernelName, decimal6]
      rfl)
  let t15 := put t14 7505 (b64 p.pageTableStride)
  have h15 : run kernel [] l g 1 t14 = some t15 :=
    runLoad64 hpre (i := 7) (off := 16) (pc := 14) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_14]
      simp only [objectLoad, param, kernelName, decimal7]
      rfl)
  let t16 := put t15 7504 (b64 p.pageTableBase)
  have h16 : run kernel [] l g 1 t15 = some t16 :=
    runLoad64 hpre (i := 7) (off := 0) (pc := 15) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_15]
      simp only [objectLoad, param, kernelName, decimal7]
      rfl)
  let t17 := put t16 7291 (.ptr 64 false (.param (param 9)) 0)
  have h17 : run kernel [] l g 1 t16 = some t17 :=
    runParamPtr (i := 9) (pc := 16) rfl rfl (by
      rw [Flow.code_16]
      simp only [param, kernelName, decimal9]
      rfl)
  let t18 := put t17 7290 (.ptr 64 false (.param (param 10)) 0)
  have h18 : run kernel [] l g 1 t17 = some t18 :=
    runParamPtr (i := 10) (pc := 17) rfl rfl (by
      rw [Flow.code_17]
      simp only [param, kernelName, decimal10]
      rfl)
  let t19 := put t18 7289 (.ptr 64 false (.param (param 11)) 0)
  have h19 : run kernel [] l g 1 t18 = some t19 :=
    runParamPtr (i := 11) (pc := 18) rfl rfl (by
      rw [Flow.code_18]
      simp only [param, kernelName, decimal11]
      rfl)
  let t20 := put t19 7506 (b64 p.cuQBase)
  have h20 : run kernel [] l g 1 t19 = some t20 :=
    runLoad64 hpre (i := 24) (off := 0) (pc := 19) (by simp [Params.objectWords]) rfl rfl (by
      rw [Flow.code_19]
      simp only [objectLoad, param, kernelName, decimal24]
      rfl)
  let t21 := put t20 7292 (b64 (l.localBase + 0))
  have h21 : run kernel [] l g 1 t20 = some t21 :=
    runLocalAdd rfl rfl rfl Flow.code_20
  let t22 := put t21 7293 (b64 (l.localBase + 32))
  have h22 : run kernel [] l g 1 t21 = some t22 :=
    runLocalAdd rfl rfl rfl Flow.code_21
  let t23 := put t22 7294 (b64 (l.localBase + 64))
  have h23 : run kernel [] l g 1 t22 = some t23 :=
    runLocalAdd rfl rfl rfl Flow.code_22
  let t24 := put t23 7295 (b64 (l.localBase + 96))
  have h24 : run kernel [] l g 1 t23 = some t24 :=
    runLocalAdd rfl rfl rfl Flow.code_23
  let t25 := put t24 1665 (b32 l.sharedBase)
  have h25 : run kernel [] l g 1 t24 = some t25 := by
    apply runPut rfl rfl Flow.code_24 rfl
    rw [execLocal_move rfl]
    have hb : l.sharedBase < 2 ^ 32 := by have := hpre.shared.2.1; omega
    change (Except.ok (put t24 1665 (.bits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase)))) :
      Exec TState) = Except.ok t25
    rw [truncBits_ofNat hb (by decide)]
    rfl
  refine ⟨t25, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · have lift {t u : TState} (hpc : t.pc < 25) (h : run kernel [] l g 1 t = some u) :
        run kernel A l g 1 t = some u := startupOne (.inl (by omega)) h
    have s1 := lift (show 0 < 25 by decide) h1
    have s2 := lift (show 1 < 25 by decide) h2
    have s3 := lift (show 2 < 25 by decide) h3
    have s4 := lift (show 3 < 25 by decide) h4
    have s5 := lift (show 4 < 25 by decide) h5
    have s6 := lift (show 5 < 25 by decide) h6
    have s7 := lift (show 6 < 25 by decide) h7
    have s8 := lift (show 7 < 25 by decide) h8
    have s9 := lift (show 8 < 25 by decide) h9
    have s10 := lift (show 9 < 25 by decide) h10
    have s11 := lift (show 10 < 25 by decide) h11
    have s12 := lift (show 11 < 25 by decide) h12
    have s13 := lift (show 12 < 25 by decide) h13
    have s14 := lift (show 13 < 25 by decide) h14
    have s15 := lift (show 14 < 25 by decide) h15
    have s16 := lift (show 15 < 25 by decide) h16
    have s17 := lift (show 16 < 25 by decide) h17
    have s18 := lift (show 17 < 25 by decide) h18
    have s19 := lift (show 18 < 25 by decide) h19
    have s20 := lift (show 19 < 25 by decide) h20
    have s21 := lift (show 20 < 25 by decide) h21
    have s22 := lift (show 21 < 25 by decide) h22
    have s23 := lift (show 22 < 25 by decide) h23
    have s24 := lift (show 23 < 25 by decide) h24
    have s25 := lift (show 24 < 25 by decide) h25
    exact run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
      (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
      (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp s1 s2)
        s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20)
        s21) s22) s23) s24) s25
  · repeat' constructor

theorem start {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m) (g : Nat) :
    ∃ t, run kernel [] l g 25 {} = some t ∧ At t 25 (abiFacts p l) :=
  startWith hpre g

end
end PTX.Kernels.TmlFa4Fwd.Prologue
