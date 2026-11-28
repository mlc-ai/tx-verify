-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.QueryAddress
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Store
import Lemmas.Flow.StoreValid

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow PTX.Proof Control

/-- **The write of a query store site** is four bytes at its lane's word. -/
public theorem query_store_at {Q L m g w d t ins o e} (hp : Pre Q L m) (i : Fin 8)
    (j : Fin 4) (site : d.site = .stq i j) (ht : (Control.code Q L g w).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (fire : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    ((∃ f, e.kind = .ub f) ∨ ∃ a bs, e.kind = .wr a bs) ∧
      ∀ a bs, e.kind = .wr a bs →
        a.loc = ⟨.shared, g / L.block, queryAddress L g i + 4 * j.val⟩ ∧ a.size = 4 := by
  rw [site] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans (fetchQueryStore i))
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have live : ∀ i : Fin 8, 746+5*i.val ∈ ctlLive (526+6*i.val) := by decide +kernel
  have found := holds_mem regs (mem_factsFrom (by rw [site]; exact live i))
  change t.regs (746+5*i.val) = some (valueOf Q L g w d (746+5*i.val)) at found
  rw [query_register hp i] at found
  have range := queryAddress_range hp g i
  have room := hp.sharedRange
  change L.sharedBase+213340≤2^18 at room
  have small : queryAddress L g i < 2^32 := by omega
  generalize Assumptions.all = A at fire
  have shape := fires_stv32 (A := A) (L := L) (g := g) (pc := (Site.stq i j).pc)
    (e := e) (o := o) (srcs := srcs i) (ik := .b) found small (.inr (.inr rfl))
  change t.sub = d.site.sub at sub
  rw [site] at sub
  change t.sub = j.val at sub
  refine ⟨(fires_stv32_kind (srcs := srcs i) (ik := .b) found small (.inr (.inr rfl)) fire).symm,
    fun a bs hk => ?_⟩
  obtain ⟨addr,size⟩ := shape fire a bs hk
  rw [sub] at addr
  exact ⟨addr, size⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue
