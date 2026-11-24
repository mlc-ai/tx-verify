-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerStoreBytes
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Base
public import Lemmas.Flow.TcLdTmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount

@[expose] public section

/-! # The values a consumer loads and stores, along its run

The accumulator values a consumer holds are the words of its loads of the tile: from the load of
chunk `ch` on, entries `16 ch` to `16 ch + 15` are that load's sixteen words, loaded with as many
accumulator arrivals as now, or one fewer past the accumulator release (`ValRel`, first part).
On a trace without undefined behaviour, the staging stores of the slice it is in wrote the packed
halves of those entries (`ValRel`, second part, with `store_bytes`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The chunks of the tile a state holds as loaded: those before the load it is at, through the
load it waits for, and all sixteen from the release through the epilogue. -/
def D.loaded (d : D) : Nat := match d.site with
  | .load j => j.val
  | .loadWait j => j.val + 1
  | .accArrive | .drain _ | .barA _ | .store .. | .barB _ | .fence _ | .tma _ | .commit _ => 16
  | _ => 0

/-- The values of a consumer's run: its loaded entries are its loads' words, and on a trace without
undefined behaviour the slice's staging stores wrote their packed halves. -/
def ValRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  (∀ ch, ch < d.loaded → ∃ kl pc vals, kl < es.length ∧
    es[kl]? = some ⟨pc, .tc (.ld (256 * accIdx L g + 16 * ch) vals .s32x32b)⟩ ∧
    (∀ w, w < 16 → vals[w]? = some (d.acc (16 * ch + w))) ∧
    arrivals (accEmpty L g (accIdx L g)) (es.take kl) + d.inEpi =
      arrivals (accEmpty L g (accIdx L g)) es) ∧
  ((∀ e ∈ es, ∀ f, e.kind ≠ .ub f) → ∀ k n, d.storePos = some (k, n) → n ≤ es.length ∧
    ∀ m, m < n → ∃ pc a bs, es[es.length - n + m]? = some ⟨pc, .wr a bs⟩ ∧
      bs = (storeWord d.acc k (m / 4) (m % 4)).toBytes)

set_option maxHeartbeats 8000000 in
/-- The address register of load `j` holds the warp group's accumulator column of chunk `j`. -/
theorem ld_addr {c : D} {t : TState} {j : Fin 16} (hat : (code L g).AtD (.inr (.cons c)) t)
    (hs : c.site = .load j) :
    t.regs (ldAddr j) = some (b32 (256 * (tidOf L g / 32 / 4) + 16 * j.val)) := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  simp only at hs hat
  subst hs
  fin_cases j
  all_goals
    simp only [ldAddr, ldAddrN]
    exact (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by cons_values))

set_option maxHeartbeats 8000000 in
/-- A step that is not a load keeps the accumulator; the loaded chunks shrink or stay, and while
some are held the epilogue flag stays, except at the release. -/
theorem next_vals {d d' : D} {e : Event} (hn : next L g d e = some (some d'))
    (hs : ∀ j, d.site ≠ .load j) :
    d'.acc = d.acc ∧ (0 < d'.loaded → d'.loaded ≤ d.loaded ∧
      (d'.inEpi = d.inEpi ∨ d.site = .accArrive)) := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case load j => exact absurd rfl (hs j)
  all_goals simp only [next] at hn
  all_goals clc_sweep hn
  all_goals simp_all [D.loaded, D.inEpi]

/-- An arrival on the accumulator's empty barrier is the release's. -/
theorem arrivals_frame {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hs : d.site ≠ .accArrive)
    (pre : List Event) :
    arrivals (accEmpty L g (accIdx L g)) (pre ++ [e]) = arrivals (accEmpty L g (accIdx L g)) pre :=
      by
  have hR := arrives_acc_site hpre hg hat hc hf
  have h0 : arrivesOn (accEmpty L g (accIdx L g)) e = false :=
    Bool.eq_false_iff.mpr fun h' => hs (hR h')
  rw [arrivals_snoc, h0]
  simp

set_option maxHeartbeats 8000000 in
/-- One step of a consumer's run keeps its values. -/
theorem valRel_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event}
    (hat : (code L g).AtD (.inr (.cons d)) t) (htid : tidOf L g < 256)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : ValRel L g d pre) : ValRel L g d' (pre ++ [e]) := by
  obtain ⟨hL, hS⟩ := hq
  have hlen : (pre ++ [e]).length = pre.length + 1 := by simp
  have hidx : ∀ kl, kl < pre.length → (pre ++ [e])[kl]? = pre[kl]? :=
    fun kl h => List.getElem?_append_left h
  have htake : ∀ kl, kl ≤ pre.length → (pre ++ [e]).take kl = pre.take kl :=
    fun kl h => List.take_append_of_le_length h
  refine ⟨fun ch hch => ?_, ?_⟩
  · by_cases hld : ∃ j, d.site = .load j
    · -- the load: chunk `j` is this event
      obtain ⟨j, hj⟩ := hld
      obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
      simp only at hj
      subst hj
      simp only [next] at hn
      split at hn
      · rename_i vals sh hk
        simp only [Option.some.injEq] at hn
        subst hn
        have hcode := code_load j
        change kernel.code[(Site.load j).pc]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans hcode)
        have hlv : vals.length = 16 := by
          rw [fires_tcLd_len (fun _ h => by cases h) hf hk]; exact ldRegs_len j
        have hreg := ld_addr hat (j := j) rfl
        have hd : isTcData e = true := by obtain ⟨pc, kd⟩ := e; simp only at hk; subst hk; rfl
        obtain ⟨vals', he'⟩ := fires_tcLd_addr hreg (by have := htid; omega) hf hd
        have hA := arrivals_frame hpre hg hat (show kernel.code[(Site.load j).pc]? =
          some _ from hcode)
          hf (by simp) pre
        simp only [D.loaded] at hch
        rcases Nat.lt_or_ge ch j.val with hlt | hge
        · obtain ⟨kl, pc, vs, hkl, h1, h2, h3⟩ := hL ch (by simpa [D.loaded] using hlt)
          refine ⟨kl, pc, vs, by omega, by rw [hidx kl hkl]; exact h1, fun w hw => ?_, ?_⟩
          · rw [h2 w hw]
            simp only [loadAcc]
            rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
          · rw [htake kl hkl.le, hA]
            simpa [D.inEpi] using h3
        · obtain rfl : ch = j.val := by omega
          refine ⟨pre.length, e.pc, vals, by omega, ?_, fun w hw => ?_, ?_⟩
          · rw [List.getElem?_append_right le_rfl]
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq]
            rw [he'] at hk ⊢
            simp only [Kind.tc.injEq, TcKind.ld.injEq] at hk
            obtain ⟨rfl, rfl, rfl⟩ := hk
            rfl
          · have hw' : 16 * j.val ≤ 16 * j.val + w ∧ 16 * j.val + w < 16 * j.val + 16 := by omega
            simp only [loadAcc, hw', and_self, ↓reduceIte,
              show 16 * j.val + w - 16 * j.val = w by omega,
              List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show w < vals.length by omega)]
            rfl
          · rw [htake _ le_rfl, hA]
            simp [D.inEpi]
      · cases hn
    · push Not at hld
      obtain ⟨hacc, hsh⟩ := next_vals hn hld
      obtain ⟨hle, hepi⟩ := hsh (by omega)
      obtain ⟨kl, pc, vs, hkl, h1, h2, h3⟩ := hL ch (by omega)
      refine ⟨kl, pc, vs, by omega, by rw [hidx kl hkl]; exact h1, fun w hw => by
        rw [h2 w hw, hacc], ?_⟩
      rw [htake kl hkl.le]
      rcases hepi with hepi | hacs
      · rw [hepi, arrivals_frame hpre hg hat hc hf (by
          intro h
          obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
          simp only at h hn hepi
          subst h
          simp only [next, Option.some.injEq] at hn
          subst hn
          simp [D.inEpi] at hepi) pre]
        exact h3
      · obtain ⟨rel, sc, rfl⟩ := accArrive_event hpre hg hacs hat.2.2.2.2 hc hf
        obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
        simp only at hacs h3 hn
        subst hacs
        simp only [next, Option.some.injEq] at hn
        subst hn
        rw [arrivals_snoc]
        simp only [D.inEpi, arrivesOn, sourceArrive] at h3 ⊢
        simp
        omega
  · intro hnu k n hpos
    have hnu' : ∀ x ∈ pre, ∀ f, x.kind ≠ .ub f :=
      fun x hx f => hnu x (List.mem_append_left _ hx) f
    have hne : ∀ f, e.kind ≠ .ub f :=
      fun f => hnu e (List.mem_append_right _ (List.mem_singleton.mpr rfl)) f
    obtain ⟨site, mm, n0, m', n', cp, ap, resp, x, acc, base⟩ := d
    cases site
    case store k0 i el =>
      obtain ⟨hk, -⟩ := store_event_all hpre hat htid hc hf (k := k0) (i := i) (el := el) rfl
      obtain ⟨a, bs, hkind⟩ : ∃ a bs, e.kind = .wr a bs :=
        hk.resolve_right (by rintro ⟨f, hf'⟩; exact hne f hf')
      have hbs := store_bytes hat htid hpre hc hf (k := k0) (i := i) (el := el) rfl a bs hkind
      obtain ⟨hle, hst⟩ := hS hnu' k0 (4 * i.val + el.val) rfl
      have hi := i.isLt
      have hel := el.isLt
      have hpos' : n = 4 * i.val + el.val + 1 ∧ k = k0 ∧ d'.acc = acc := by
        simp only [next] at hn
        split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
          simp only [D.storePos, Option.some.injEq, Prod.mk.injEq] at hpos <;>
          exact ⟨by omega, by omega, rfl⟩
      obtain ⟨hn1, hk1, hacc⟩ := hpos'
      subst hn1 hk1
      rw [hacc]
      obtain ⟨epc, ek⟩ := e
      simp only at hkind
      subst hkind
      refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun m hm => ?_⟩
      have hidx : (pre ++ [(⟨epc, .wr a bs⟩ : Event)]).length - (4 * i.val + el.val + 1) + m =
          pre.length - (4 * i.val + el.val) + m := by
        simp only [List.length_append, List.length_singleton]; omega
      rw [hidx]
      by_cases hm' : m < 4 * i.val + el.val
      · obtain ⟨pc, a', bs', h1, h2⟩ := hst m hm'
        refine ⟨pc, a', bs', ?_, h2⟩
        rw [List.getElem?_append_left (by omega)]
        exact h1
      · have hmeq : m = 4 * i.val + el.val := by omega
        refine ⟨epc, a, bs, ?_, ?_⟩
        · rw [show pre.length - (4 * i.val + el.val) + m = pre.length by omega]
          simp
        · rw [hbs, hmeq, show (4 * i.val + el.val) / 4 = i.val by omega,
            show (4 * i.val + el.val) % 4 = el.val by omega]
    case barA k0 =>
      simp only [next, Option.some.injEq] at hn
      subst hn
      simp only [D.storePos, Option.some.injEq, Prod.mk.injEq] at hpos
      obtain ⟨-, rfl⟩ := hpos
      exact ⟨Nat.zero_le _, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
    all_goals exfalso
    all_goals clear hS hc hf hat hnu hnu' hne hL
    all_goals simp only [next] at hn
    clc_sweep hn
    all_goals simp_all [D.storePos]

end Consumer

end

end PTX.Kernels.Fp16Gemm8192.Proof
