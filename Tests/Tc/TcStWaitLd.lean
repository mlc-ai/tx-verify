-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run

namespace PTX.Tests.TcStWaitLd
noncomputable section

private def A : List Assumption := [{
  name := "test load completion before a store"
  statement := "The first store follows load completion."
  tcStWaitLd := (· == 2) }]

private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
private def t : TState := {
  pc := 2
  regs := fun _ => some (.bits 32 0) }
private def op : Op := .tcSt 0 [.reg 1] .s32x32b
private def K : Kernel := {
  name := "wait-before-store"
  params := []
  code := [⟨none, .exit⟩, ⟨none, .exit⟩, ⟨none, op⟩, ⟨none, .exit⟩] }
private def m : Tmpl := .tc (.st 0 [.bits 32 0] .s32x32b) { t with pc := 3 }

theorem waitAtOriginalPc : eventTmpl A L 0 t op = .tc .waitLd { t with sub := 1 } := rfl

theorem storeAfterWait : eventTmpl A L 0 { t with sub := 1 } op = m := rfl

theorem waitThenStore :
    Run K A L 0 t [⟨2, .tc .waitLd⟩, ⟨2, .tc (.st 0 [.bits 32 0] .s32x32b)⟩]
      (some { t with pc := 3 }) :=
  .step .refl ⟨_, rfl, rfl, rfl⟩ (.step .refl ⟨_, rfl, rfl, rfl⟩ (.nil _))

theorem defaultStoresImmediately : eventTmpl [] L 0 t op = m := rfl

theorem unselectedStore : eventTmpl A L 0 { t with pc := 3 } op =
    eventTmpl [] L 0 { t with pc := 3 } op := rfl

theorem hookIsStoreOnly : eventTmpl A L 0 t .tcWaitLd = eventTmpl [] L 0 t .tcWaitLd := rfl

end

end PTX.Tests.TcStWaitLd
