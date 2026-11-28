-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Site
public import Kernels.InklingRelDecode.Proof.Lib.AlphaAt
public import Kernels.InklingRelDecode.Proof.Lib.Havoc
public import Lemmas.Flow.ItemsU
public import Lemmas.Flow.ReachSegU
public import Lemmas.Flow.ReachFrameGuard
public import Lemmas.Flow.ShflSrc
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The rescale factor of a round, from the two halves of the row maximum

From the shuffle at pc 1838 (the row's own half `sent` in register 1520, the partner's `recv` in
1521) to the shuffle at pc 2234: the new maximum, the test and the factor (pcs 1839 to 1846), then
code that writes none of them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem req_alpha (V : Nat → Value) : xReq V Lib.alphaItems = true := by
  simp [Lib.alphaItems, Lib.alphaRest, Lib.maxItem, xReq, XItem.req, OItem.req, XItem.upd,
    XItem.vals, OItem.vals, isPred, isRegOrF32, fcmpBase, Function.update]

/-- The registers before the run and the values the machine holds. -/
def alphaV (L : Launch) (m sent recv : Value) (r : Nat) : Value :=
  if r = 1520 then sent else if r = 1521 then recv else if r = 1914 then m
  else if r = 498 then scaleW L else b32 0

/-- **The run of pcs 1839 to 1846** from the halves and the carried maximum. -/
theorem alpha_run (m sent recv : Value) :
    SegU kernel Assumptions.all L g 1839 (factsFrom [1520, 1521, 1914, 498] (alphaV L m sent recv))
      1847 (factsFrom [498, 1914, 1522, 168, 507] (xFinal (alphaV L m sent recv) Lib.alphaItems)) :=
  SegU.of_items Lib.alpha_at (by decide +kernel) (by decide +kernel) (req_alpha _)
    (by decide +kernel)

/-- The run also leaves the maximum used (register 1523). -/
theorem alpha_run6 (m sent recv : Value) :
    SegU kernel Assumptions.all L g 1839 (factsFrom [1520, 1521, 1914, 498] (alphaV L m sent recv))
      1847 (factsFrom [498, 1914, 1522, 168, 507, 1523]
        (xFinal (alphaV L m sent recv) Lib.alphaItems)) :=
  SegU.of_items Lib.alpha_at (by decide +kernel) (by decide +kernel) (req_alpha _)
    (by decide +kernel)

theorem alpha_mxeq {V : Nat → Value} {m sent recv : Value} (h1 : V 1914 = m)
    (h2 : V 1520 = sent) (h3 : V 1521 = recv) :
    Lib.maxItem.upd V 1522 = Lib.mxWord m sent recv := by
  unfold Lib.mxWord
  exact Lib.xFinal_congr (S := [1914, 1520, 1521]) (items := [Lib.maxItem]) (by decide)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [h1, h2, h3]) 1522
    (Or.inl (by simp [xWrites, XItem.writes, Lib.maxItem]))

/-- The values of the registers the rescale run writes, from any registers that hold its inputs. -/
theorem alpha_fin {V : Nat → Value} {m sent recv : Value} (h1 : V 1914 = m) (h2 : V 1520 = sent)
    (h3 : V 1521 = recv) (h4 : V 498 = scaleW L) {r : Nat}
    (hr : r = 168 ∨ r = 507 ∨ r = 1523) :
    xFinal V Lib.alphaItems r = Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r := by
  have rest : xFinal V Lib.alphaItems r = xFinal (Lib.maxItem.upd V) Lib.alphaRest r := rfl
  rw [rest]
  refine Lib.xFinal_congr (S := [1914, 498, 1522]) (items := Lib.alphaRest) (by decide)
    (fun x hx => ?_) _ (Or.inl (by rcases hr with rfl | rfl | rfl <;> decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simp [XItem.upd, Lib.maxItem, XItem.vals, Function.update_of_ne, h1, Lib.alphaIn]
  · simp [XItem.upd, Lib.maxItem, XItem.vals, Function.update_of_ne, h4, Lib.alphaIn]
  · simp only [Lib.alphaIn]
    simpa using alpha_mxeq h1 h2 h3

theorem alpha_fin_v (m sent recv : Value) {r : Nat} (hr : r = 168 ∨ r = 507 ∨ r = 1523) :
    xFinal (alphaV L m sent recv) Lib.alphaItems r =
      Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r :=
  alpha_fin (V := alphaV L m sent recv) (m := m) (sent := sent) (recv := recv)
    (by simp [alphaV]) (by simp [alphaV]) (by simp [alphaV]) (by simp [alphaV]) hr

theorem alpha_o498 (m sent recv : Value) :
    xFinal (alphaV L m sent recv) Lib.alphaItems 498 = scaleW L := by
  rw [Lib.xFinal_other (by decide)]
  simp [alphaV]

theorem alpha_o1914 (m sent recv : Value) :
    xFinal (alphaV L m sent recv) Lib.alphaItems 1914 = m := by
  rw [Lib.xFinal_other (by decide)]
  simp [alphaV]

theorem alpha_o1522 (m sent recv : Value) :
    xFinal (alphaV L m sent recv) Lib.alphaItems 1522 = Lib.mxWord m sent recv := by
  have rest : xFinal (alphaV L m sent recv) Lib.alphaItems 1522 =
      xFinal (Lib.maxItem.upd (alphaV L m sent recv)) Lib.alphaRest 1522 := rfl
  rw [rest, Lib.xFinal_other (by decide)]
  exact alpha_mxeq (V := alphaV L m sent recv) (m := m) (sent := sent) (recv := recv)
    (by simp [alphaV]) (by simp [alphaV]) (by simp [alphaV])

/-- The run's values are the data facts of the round. -/
theorem alpha_facts (m sent recv : Value) :
    factsFrom [498, 1914, 1522, 168, 507] (xFinal (alphaV L m sent recv) Lib.alphaItems) =
      dFS L .shfl6 { m := m, mx := Lib.mxWord m sent recv } := by
  simp only [factsFrom, List.map_cons, List.map_nil, dFS, inRound, alphaFacts,
    alpha_o498 (L := L) m sent recv, alpha_o1914 (L := L) m sent recv,
    alpha_o1522 (L := L) m sent recv,
    alpha_fin_v (L := L) m sent recv (Or.inl rfl),
    alpha_fin_v (L := L) m sent recv (Or.inr (Or.inl rfl))]
  rfl

/-- **From the shuffle of pc 1838 to the one of pc 2234**, the round's facts hold at the next
event. -/
theorem alpha_reach (m sent recv : Value) :
    Reach kernel Assumptions.all L g 1839
      [(1520, sent), (1521, recv), (1914, m), (498, scaleW L)]
      (dFS L .shfl6 { m := m, mx := Lib.mxWord m sent recv }) := by
  have p1 := alpha_run (L := L) (g := g) m sent recv
  rw [alpha_facts] at p1
  have p2 : SegU kernel Assumptions.all L g 1847
      (dFS L .shfl6 { m := m, mx := Lib.mxWord m sent recv }) 2234
      (dFS L .shfl6 { m := m, mx := Lib.mxWord m sent recv }) :=
    SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by decide) (by decide +kernel)
      (by rw [dFS_keys]; decide +kernel) (fun _ h => h)
  have p3 : Reach kernel Assumptions.all L g 2234
      (dFS L .shfl6 { m := m, mx := Lib.mxWord m sent recv })
      (dFS L .shfl6 { m := m, mx := Lib.mxWord m sent recv }) :=
    reach_frameSetG (S := []) Lib.rulesFrame (by rw [dFS_keys]; decide +kernel)
      (fun _ h => nomatch h) (by decide +kernel) (fun _ h => h)
  refine Reach.weaken_start (Code.SegU.reach_then (p1.comp p2) p3) fun R h => ?_
  simpa [factsFrom, alphaV] using h

/-- **The data step of the shuffle at pc 1838**: the new maximum is the maximum of the carried one
and the two halves, and the round's facts follow. -/
theorem data_shfl5 {d : D} (hs : d.c.site = .shfl5) : DataStep (code e L g) (dF L) d := by
  intro t ev u d' ins hat hi hc' hf hn
  have pc : (code e L g).pc d = 1838 := by
    change d.c.site.pc = 1838
    rw [hs]
    rfl
  rw [pc] at hc' hf
  rw [Flow.code_shfl_5] at hc'
  obtain rfl := Option.some.inj hc'
  obtain ⟨sent, bv, cv, recv, ok, hr, rfl, rfl⟩ := fires_shfl_src (p := none) hf
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  obtain ⟨hpc, hsub, hacc, hft, hreg⟩ := hat
  have hF := facts_dF _ hreg
  have hd : dF L ⟨{ d.c with site := .shfl6 },
      record L d ⟨1838, .shfl .bfly sent bv cv recv ok⟩ .shfl6⟩ =
      dFS L .shfl6 { m := d.v.m, mx := Lib.mxWord d.v.m sent recv } := by
    simp only [dF, record, hs]
    rfl
  rw [hd]
  have h1914 : t.regs 1914 = some d.v.m := holds_mem hF (by simp [dF, dFS, hs])
  have h498 : t.regs 498 = some (scaleW L) := holds_mem hF (by simp [dF, dFS, hs])
  have key := alpha_reach (L := L) (g := g) d.v.m sent recv
  refine key _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [PTX.next, setReg, hpc]
    rw [hs]
    rfl
  · simp [PTX.next, setReg, hsub]
  · simp [PTX.next, setReg, hacc]
  · simp [PTX.next, setReg, hft]
  · simp [PTX.next, setReg, Holds, Function.update_of_ne, h1914, h498, hr]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
