-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX MbarRow

structure MbarRows (Q : Params) (L : Launch) (X : Execution) : Prop where
  startup : MbarRow.Startup Q L X
  prologue : MbarRow.Prologue Q L X
  softmax : MbarRow.Softmax Q L X
  epilogue : MbarRow.Epilogue Q L X
  dispatch : MbarRow.Dispatch Q L X
  loader : MbarRow.Loader Q L X
  mma : MbarRow.Mma Q L X
  place : MbarRow.Place Q L X

inductive MbarUse (Q : Params) (L : Launch) (X : Execution) (g k : Nat)
    (e : Event) (l : Loc) : Prop where
  | startup (atPc : StartupAt L g e.pc) (use : StartupUse L X g k e l)
  | prologue (atPc : PrologueAt L g e.pc) (use : PrologueUse L X g k e l)
  | softmax (atPc : SoftmaxAt L g e.pc) (use : SoftmaxUse L X g k e l)
  | epilogue (atPc : EpilogueAt L g e.pc) (use : EpilogueUse L X g k e l)
  | dispatch (atPc : DispatchAt L g e.pc) (use : DispatchUse L X g k e l)
  | loader (atPc : LoaderAt L g e.pc) (use : LoaderUse Q L X g k e l)
  | mma (atPc : MmaAt L g e.pc) (use : MmaUse L X g k e l)

theorem mbar_use {Q : Params} {L : Launch} {X : Execution} {g k : Nat} {e : Event} {l : Loc}
    (rows : MbarRows Q L X) (hg : g < L.threads) (he : X.get (g,k) = some e)
    (hm : Frame.MbarOf e l) : MbarUse Q L X g k e l := by
  rcases rows.place hg he hm with h | h | h | h | h | h | h
  · exact .startup h (rows.startup hg he h hm)
  · exact .prologue h (rows.prologue.2 hg he h hm)
  · exact .softmax h (rows.softmax hg he h hm)
  · exact .epilogue h (rows.epilogue hg he h hm)
  · exact .dispatch h (rows.dispatch hg he h hm)
  · exact .loader h (rows.loader hg he h hm)
  · exact .mma h (rows.mma hg he h hm)

end PTX.Kernels.InklingRelDecode.Proof
