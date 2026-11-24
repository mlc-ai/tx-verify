-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Code
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.AccessLocal

@[expose] public section

/-!
# The dynamic stores of the code write the thread's own CTA

`Flow.fires_write_loc` puts a shared write of a store that is not a dynamic access in the thread's
own CTA. The code's dynamic stores are all stores to the CTA's shared memory at a symbol address
(`kernel_dynWrite_sharedSym`), whose location `accessLoc` puts in the thread's own CTA
(`sharedSym_write_cta`). So every shared write of a thread is in its own CTA, whatever the thread's
registers hold.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Flow

/-- A store to the CTA's shared memory at a symbol address. -/
def sharedSymStore : Op → Bool
  | .mem a => match a.kind, a.space, a.addr.base with
    | .store, some (.shared .cta), .sharedSym _ => true
    | _, _, _ => false
  | _ => false

/-- **Every dynamic store of the code is a store to the CTA's shared memory at a symbol
address.** -/
theorem kernel_dynWrite_sharedSym :
    OpPcsFast kernel.code (fun op => dynamicAccess op && writeOp op && !sharedSymStore op) [] =
      true := by
  decide +kernel

theorem sharedSymStore_form {op : Op} (h : sharedSymStore op = true) :
    ∃ a o, op = .mem a ∧ a.kind = .store ∧ a.space = some (.shared .cta) ∧
      a.addr.base = .sharedSym o := by
  cases op with
  | mem a =>
    refine ⟨a, ?_⟩
    simp only [sharedSymStore] at h
    cases hk : a.kind <;> cases hs : a.space <;> cases hb : a.addr.base <;>
      simp_all
    all_goals (revert h; split <;> simp_all)
  | _ => simp [sharedSymStore] at h

/-- A store's template that writes has its footprint as the write's. -/
theorem accessTmpl_store_write {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {acc : Acc} {bs : List Byte} {u : TState} (hk : a.kind = .store)
    (h : accessTmpl A L g t a = .write acc bs u) : accessAcc L g t a = .ok acc := by
  simp only [accessTmpl, hk] at h
  cases hacc : accessAcc L g t a with
  | error f => simp [hacc] at h
  | ok acc' =>
    simp only [hacc] at h
    cases hs : a.srcs[t.sub]? with
    | none => simp [hs] at h
    | some o =>
      simp only [hs] at h
      cases hv : (readValue L g t a.elem.width o >>= storeValue a.elem.width) with
      | error f => simp [hv] at h
      | ok v =>
        simp only [hv, Tmpl.write.injEq] at h
        rw [h.1]

/-- The footprint of an access to the CTA's shared memory at a symbol address is in the thread's
own CTA. -/
theorem accessAcc_sharedSym {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {o : Nat}
    {acc : Acc} (hsp : a.space = some (.shared .cta)) (hb : a.addr.base = .sharedSym o)
    (h : accessAcc L g t a = .ok acc) : acc.loc.cta = g / L.block := by
  have hmap : ∀ {α : Type} {f : α → Acc} {x : Exec α} {r : Acc}, f <$> x = .ok r →
      ∃ y, x = .ok y ∧ f y = r := by
    intro α f x r hx
    cases x with
    | error e => simp at hx
    | ok y => exact ⟨y, rfl, by simpa using hx⟩
  have hl : accessLoc L g t a = .ok ⟨.shared, g / L.block,
      wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + o)) a.addr.off⟩ := by
    simp [accessLoc, hsp, hb, pure, Except.pure]
  unfold accessAcc at h
  simp only [bind, Except.bind, hl] at h
  repeat' (first | split at h | contradiction)
  obtain ⟨acc0, h0, he⟩ := hmap h
  obtain ⟨-, h2⟩ := elemAcc_local h0
  subst he
  simp only [semAcc_loc]
  exact h2

/-- **A write of a store to the CTA's shared memory at a symbol address is in the thread's own
CTA.** -/
theorem sharedSym_write_cta {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {o pc epc : Nat} {acc : Acc} {bs : List Byte} {u : Option TState}
    (hk : a.kind = .store) (hsp : a.space = some (.shared .cta)) (hb : a.addr.base = .sharedSym o)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) ⟨epc, .wr acc bs⟩ u) :
    acc.loc.cta = g / L.block := by
  rcases fires_write_tmpl hf with ⟨u', hm⟩ | ⟨u', hm, -⟩
  swap
  · have := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
    simp only [eventTmpl] at hm
    rw [hm] at this
    exact this.elim
  simp only [eventTmpl, memTmpl] at hm
  split at hm
  · rename_i hb'
    rw [hb] at hb'
    cases hb'
  · exact absurd hm atomTmpl_noWrite
  · split at hm
    · exact accessAcc_sharedSym hsp hb (accessTmpl_store_write hk hm)
    · cases hm

/-- **A shared write of an instruction of the code is in the thread's own CTA.** -/
theorem code_write_cta {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    {pc epc : Nat} {acc : Acc} {bs : List Byte} {u : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl A L g t ins.op) ⟨epc, .wr acc bs⟩ u)
    (hsp : acc.loc.space = .shared) : acc.loc.cta = g / L.block := by
  rcases fires_write_loc hf rfl with ⟨-, h2⟩ | hd
  · exact h2 hsp
  · have hwo := fires_write_op hf (rfl : (⟨epc, .wr acc bs⟩ : Event).kind = .wr acc bs)
    by_cases hs : sharedSymStore ins.op = true
    · obtain ⟨a, o, hop, hk, hsp', hb⟩ := sharedSymStore_form hs
      rw [hop] at hf
      exact sharedSym_write_cta hk hsp' hb hf
    · have := OpPcsFast.mem kernel_dynWrite_sharedSym hc (by simp [hd, hwo, hs])
      simp at this

end PTX.Kernels.InklingRelDecode.Proof.Interface
