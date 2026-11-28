-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # The location a scalar global store writes

A proof tool. A scalar `st.global.b32` whose 64-bit base register holds the aligned address `a`
writes the four bytes at `a` of global memory (`fires_st_global`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A scalar `st.global.b32` through a 64-bit base register: what `fires_st_global` needs of
the instruction. -/
def GlobalStore (a : MemAccess) (base src : Nat) : Prop :=
  a.rule = some .threadAccess ∧ a.locSpace? = some .global ∧ a.addr.base = .reg base 64 ∧
    a.kind = .store ∧ a.sem = .weak ∧ a.elem.width = 32 ∧ a.addr.off = 0 ∧ a.srcs = [.reg src]

instance (a : MemAccess) (base src : Nat) : Decidable (GlobalStore a base src) := by
  unfold GlobalStore; infer_instance

theorem fires_st_global {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {u : Option TState}
    {base a src : Nat} {pc : Nat} {e : Event} {acc : Acc} {bs : List Byte} {m : MemAccess}
    (hm : GlobalStore m base src)
    (hr : t.regs base = some (b64 a)) (ha : a < 2 ^ 64) (hal : a % 4 = 0) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem m)) e u)
    (hk : e.kind = .wr acc bs) : acc.loc = ⟨.global, 0, a⟩ ∧ acc.size = 4 := by
  obtain ⟨hrule, hsp, hb, hkind, hsem, hw, hoff, hsrc⟩ := hm
  rw [eventTmpl, memTmpl_store (sp := .global) (base := base) (w := 64) hrule hsp hb hkind
    hsem, hw, hoff, hsrc] at hf
  change Fires pc (storeTmpl L g t .global 32 base 0 [.reg src]) e u at hf
  cases hv : t.regs src with
  | none =>
    unfold storeTmpl at hf
    rw [effAddr_global hr ha] at hf
    simp [hs, elemAcc, readValue, readReg, hv, Fires, bind, Except.bind, pure, Except.pure, hal,
      throw, throwThe, MonadExceptOf.throw] at hf
    rw [hf.1] at hk
    cases hk
  | some v =>
    have := storeTmpl_global (L := L) (g := g) (w := 32) (src := src) hs hr ha
      (by norm_num) (by simpa using hal) hv
    rw [this] at hf
    cases hs' : storeValue 32 v with
    | error f =>
      simp only [hs', Fires] at hf
      rw [hf.1] at hk; cases hk
    | ok v' =>
      simp only [hs', Fires] at hf
      rw [hf.1] at hk
      obtain ⟨rfl, -⟩ := Kind.wr.inj hk
      exact ⟨rfl, rfl⟩

end
end PTX.Flow
