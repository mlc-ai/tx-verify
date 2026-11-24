-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ReadLast
public import Kernels.InklingRelDecode.Proof.Interface.PrefixLdRng

@[expose] public section

/-!
# The prefix form of the thread facts

The dependency order of an execution (`PrefixOrder`), the local forms of the thread facts that
ask only for the tracking of the event they are about (`PrefixLocal`), and the induction along
the dependency order that proves tracking and the launch bytes of the input reads from the local
successor fact (`PrefixTrack`), its discharge at the prologue's request-word and query loads
(`PrefixPro`), `Premises` from what is left (`PrefixPremises`) and the reads-from step of the
shared-word facts (`PrefixRf`). This umbrella imports
`Protocol.MbarWords`, so `Interface.All` and the protocol modules do not import it.
-/
