-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScope00
public import Kernels.TmlFa4Fwd.Audit.DecodeScope01
public import Kernels.TmlFa4Fwd.Audit.DecodeScope02
public import Kernels.TmlFa4Fwd.Audit.DecodeScope03
public import Kernels.TmlFa4Fwd.Audit.DecodeScope04
public import Kernels.TmlFa4Fwd.Audit.DecodeScope05
public import Kernels.TmlFa4Fwd.Audit.DecodeScope06
public import Kernels.TmlFa4Fwd.Audit.DecodeScope07
public import Kernels.TmlFa4Fwd.Audit.DecodeScope08
public import Kernels.TmlFa4Fwd.Audit.DecodeScope09
public import Kernels.TmlFa4Fwd.Audit.DecodeScope10
public import Kernels.TmlFa4Fwd.Audit.DecodeScope11
public import Kernels.TmlFa4Fwd.Audit.DecodeScope12
public import Kernels.TmlFa4Fwd.Audit.DecodeScope13
public import Kernels.TmlFa4Fwd.Audit.DecodeScope14
public import Kernels.TmlFa4Fwd.Audit.DecodeScope15
public import Kernels.TmlFa4Fwd.Audit.DecodeScope16
public import Kernels.TmlFa4Fwd.Audit.DecodeScope17
public import Kernels.TmlFa4Fwd.Audit.DecodeScope18
public import Kernels.TmlFa4Fwd.Audit.DecodeScope19

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000
set_option Elab.async false

def resolved : List Statement :=
  resolved0 ++ (resolved1 ++ (resolved2 ++ (resolved3 ++ (resolved4 ++ (resolved5 ++ (resolved6 ++
                (resolved7 ++ (resolved8 ++ (resolved9 ++ (resolved10 ++ (resolved11 ++ (resolved12
                            ++ (resolved13 ++ (resolved14 ++ (resolved15 ++ (resolved16 ++
                                    (resolved17 ++ (resolved18 ++ (resolved19)))))))))))))))))))

private theorem source_body_left : source.body = (raw0 ++ raw1 ++ raw2 ++ raw3 ++ raw4 ++ raw5 ++
    raw6 ++ raw7 ++ raw8 ++ raw9 ++ raw10 ++ raw11 ++ raw12 ++ raw13 ++ raw14 ++ raw15 ++ raw16 ++
    raw17 ++ raw18 ++ raw19) := rfl

private theorem source_body_right : source.body = (raw0 ++ (raw1 ++ (raw2 ++ (raw3 ++ (raw4 ++ (raw5
              ++ (raw6 ++ (raw7 ++ (raw8 ++ (raw9 ++ (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (raw14
                                ++ (raw15 ++
                                  (raw16 ++ (raw17 ++ (raw18 ++ (raw19)))))))))))))))))))) := by
  simp only [source_body_left, List.append_assoc]

private theorem depth_0 : scopeDepth raw0 = 1 := by kernel_rfl
private theorem depth_1 : scopeDepth raw1 = 2 := by kernel_rfl
private theorem depth_2 : scopeDepth raw2 = 2 := by kernel_rfl
private theorem depth_3 : scopeDepth raw3 = 2 := by kernel_rfl
private theorem depth_4 : scopeDepth raw4 = 2 := by kernel_rfl
private theorem depth_5 : scopeDepth raw5 = 2 := by kernel_rfl
private theorem depth_6 : scopeDepth raw6 = 2 := by kernel_rfl
private theorem depth_7 : scopeDepth raw7 = 2 := by kernel_rfl
private theorem depth_8 : scopeDepth raw8 = 1 := by kernel_rfl
private theorem depth_9 : scopeDepth raw9 = 1 := by kernel_rfl
private theorem depth_10 : scopeDepth raw10 = 2 := by kernel_rfl
private theorem depth_11 : scopeDepth raw11 = 1 := by kernel_rfl
private theorem depth_12 : scopeDepth raw12 = 2 := by kernel_rfl
private theorem depth_13 : scopeDepth raw13 = 2 := by kernel_rfl
private theorem depth_14 : scopeDepth raw14 = 2 := by kernel_rfl
private theorem depth_15 : scopeDepth raw15 = 2 := by kernel_rfl
private theorem depth_16 : scopeDepth raw16 = 2 := by kernel_rfl
private theorem depth_17 : scopeDepth raw17 = 2 := by kernel_rfl
private theorem depth_18 : scopeDepth raw18 = 2 := by kernel_rfl
private theorem depth_19 : scopeDepth raw19 = 2 := by kernel_rfl

private theorem source_depth : scopeDepth source.body = rootFuel + 1 := by
  simp only [source_body_right, scopeDepth_append, depth_0, depth_1, depth_2, depth_3, depth_4,
      depth_5, depth_6, depth_7, depth_8, depth_9, depth_10, depth_11, depth_12, depth_13, depth_14,
      depth_15, depth_16, depth_17, depth_18, depth_19]
  rfl

private theorem resolved_tail_19 :
    resolveScopePart (resolveScopes rootFuel) (raw19) rootBindings "" 8831 =
      .ok (resolved19) :=
  resolved_19

private theorem resolved_tail_18 :
    resolveScopePart (resolveScopes rootFuel) (raw18 ++ (raw19)) rootBindings "" 8331 =
      .ok (resolved18 ++ (resolved19)) :=
  resolveScopePart_append resolved_18 resolved_tail_19

private theorem resolved_tail_17 :
    resolveScopePart (resolveScopes rootFuel) (raw17 ++ (raw18 ++ (raw19))) rootBindings "" 7831 =
      .ok (resolved17 ++ (resolved18 ++ (resolved19))) :=
  resolveScopePart_append resolved_17 resolved_tail_18

private theorem resolved_tail_16 :
    resolveScopePart (resolveScopes rootFuel)
        (raw16 ++ (raw17 ++ (raw18 ++ (raw19)))) rootBindings "" 7325 =
      .ok (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19)))) :=
  resolveScopePart_append resolved_16 resolved_tail_17

private theorem resolved_tail_15 :
    resolveScopePart (resolveScopes rootFuel)
        (raw15 ++ (raw16 ++ (raw17 ++ (raw18 ++ (raw19))))) rootBindings "" 6867 =
      .ok (resolved15 ++ (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19))))) :=
  resolveScopePart_append resolved_15 resolved_tail_16

private theorem resolved_tail_14 :
    resolveScopePart (resolveScopes rootFuel)
        (raw14 ++ (raw15 ++ (raw16 ++ (raw17 ++ (raw18 ++ (raw19)))))) rootBindings "" 6403 =
      .ok (resolved14 ++
          (resolved15 ++ (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19)))))) :=
  resolveScopePart_append resolved_14 resolved_tail_15

private theorem resolved_tail_13 :
    resolveScopePart (resolveScopes rootFuel) (raw13 ++
        (raw14 ++ (raw15 ++ (raw16 ++ (raw17 ++ (raw18 ++ (raw19))))))) rootBindings "" 5939 =
      .ok (resolved13 ++ (resolved14 ++
            (resolved15 ++ (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19))))))) :=
  resolveScopePart_append resolved_13 resolved_tail_14

private theorem resolved_tail_12 :
    resolveScopePart (resolveScopes rootFuel) (raw12 ++ (raw13 ++
          (raw14 ++ (raw15 ++ (raw16 ++ (raw17 ++ (raw18 ++ (raw19)))))))) rootBindings "" 5487 =
      .ok (resolved12 ++ (resolved13 ++ (resolved14 ++
              (resolved15 ++ (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19)))))))) :=
  resolveScopePart_append resolved_12 resolved_tail_13

private theorem resolved_tail_11 :
    resolveScopePart (resolveScopes rootFuel) (raw11 ++ (raw12 ++ (raw13 ++
            (raw14 ++ (raw15 ++ (raw16 ++ (raw17 ++ (raw18 ++ (raw19))))))))) rootBindings "" 4975 =
      .ok (resolved11 ++ (resolved12 ++ (resolved13 ++ (resolved14 ++
                (resolved15 ++ (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19))))))))) :=
  resolveScopePart_append resolved_11 resolved_tail_12

private theorem resolved_tail_10 :
    resolveScopePart (resolveScopes rootFuel) (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (raw14 ++
                (raw15 ++ (raw16 ++ (raw17 ++ (raw18 ++ (raw19)))))))))) rootBindings "" 4481 =
      .ok (resolved10 ++ (resolved11 ++ (resolved12 ++ (resolved13 ++ (resolved14 ++ (resolved15 ++
                    (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19)))))))))) :=
  resolveScopePart_append resolved_10 resolved_tail_11

private theorem resolved_tail_9 :
    resolveScopePart (resolveScopes rootFuel) (raw9 ++ (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (
                  raw14 ++
                  (raw15 ++ (raw16 ++ (raw17 ++ (raw18 ++ (raw19))))))))))) rootBindings "" 3969 =
      .ok (resolved9 ++ (resolved10 ++ (resolved11 ++ (resolved12 ++ (resolved13 ++ (resolved14 ++
                    (resolved15 ++
                      (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19))))))))))) :=
  resolveScopePart_append resolved_9 resolved_tail_10

private theorem resolved_tail_8 :
    resolveScopePart (resolveScopes rootFuel) (raw8 ++ (raw9 ++ (raw10 ++ (raw11 ++ (raw12 ++ (raw13
                  ++ (raw14 ++ (raw15 ++
                      (raw16 ++ (raw17 ++ (raw18 ++ (raw19)))))))))))) rootBindings "" 3457 =
      .ok (resolved8 ++ (resolved9 ++ (resolved10 ++ (resolved11 ++ (resolved12 ++ (resolved13 ++
                    (resolved14 ++ (resolved15 ++
                        (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19)))))))))))) :=
  resolveScopePart_append resolved_8 resolved_tail_9

private theorem resolved_tail_7 :
    resolveScopePart (resolveScopes rootFuel) (raw7 ++ (raw8 ++ (raw9 ++ (raw10 ++ (raw11 ++ (raw12
                  ++ (raw13 ++ (raw14 ++ (raw15 ++
                        (raw16 ++ (raw17 ++ (raw18 ++ (raw19))))))))))))) rootBindings "" 2963 =
      .ok (resolved7 ++ (resolved8 ++ (resolved9 ++ (resolved10 ++ (resolved11 ++ (resolved12 ++ (
                      resolved13 ++ (resolved14 ++ (resolved15 ++
                          (resolved16 ++ (resolved17 ++ (resolved18 ++ (resolved19))))))))))))) :=
  resolveScopePart_append resolved_7 resolved_tail_8

private theorem resolved_tail_6 :
    resolveScopePart (resolveScopes rootFuel) (raw6 ++ (raw7 ++ (raw8 ++ (raw9 ++ (raw10 ++ (raw11
                  ++ (raw12 ++ (raw13 ++ (raw14 ++ (raw15 ++
                          (raw16 ++ (raw17 ++ (raw18 ++ (raw19)))))))))))))) rootBindings "" 2463 =
      .ok (resolved6 ++ (resolved7 ++ (resolved8 ++ (resolved9 ++ (resolved10 ++ (resolved11 ++ (
                      resolved12 ++ (resolved13 ++ (resolved14 ++ (resolved15 ++ (resolved16 ++
                              (resolved17 ++ (resolved18 ++ (resolved19)))))))))))))) :=
  resolveScopePart_append resolved_6 resolved_tail_7

private theorem resolved_tail_5 :
    resolveScopePart (resolveScopes rootFuel) (raw5 ++ (raw6 ++ (raw7 ++ (raw8 ++ (raw9 ++ (raw10 ++
                  (raw11 ++ (raw12 ++ (raw13 ++ (raw14 ++ (raw15 ++ (raw16 ++
                              (raw17 ++ (raw18 ++ (raw19))))))))))))))) rootBindings "" 2279 =
      .ok (resolved5 ++ (resolved6 ++ (resolved7 ++ (resolved8 ++ (resolved9 ++ (resolved10 ++ (
                      resolved11 ++ (resolved12 ++ (resolved13 ++ (resolved14 ++ (resolved15 ++ (
                                resolved16 ++
                                (resolved17 ++ (resolved18 ++ (resolved19))))))))))))))) :=
  resolveScopePart_append resolved_5 resolved_tail_6

private theorem resolved_tail_4 :
    resolveScopePart (resolveScopes rootFuel) (raw4 ++ (raw5 ++ (raw6 ++ (raw7 ++ (raw8 ++ (raw9 ++
                  (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (raw14 ++ (raw15 ++ (raw16 ++
                                (raw17 ++ (raw18 ++ (raw19)))))))))))))))) rootBindings "" 1953 =
      .ok (resolved4 ++ (resolved5 ++ (resolved6 ++ (resolved7 ++ (resolved8 ++ (resolved9 ++ (
                      resolved10 ++ (resolved11 ++ (resolved12 ++ (resolved13 ++ (resolved14 ++ (
                                resolved15 ++ (resolved16 ++
                                  (resolved17 ++ (resolved18 ++ (resolved19)))))))))))))))) :=
  resolveScopePart_append resolved_4 resolved_tail_5

private theorem resolved_tail_3 :
    resolveScopePart (resolveScopes rootFuel) (raw3 ++ (raw4 ++ (raw5 ++ (raw6 ++ (raw7 ++ (raw8 ++
                  (raw9 ++ (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (raw14 ++ (raw15 ++ (raw16 ++
                                  (raw17 ++ (raw18 ++ (raw19))))))))))))))))) rootBindings "" 1470 =
      .ok (resolved3 ++ (resolved4 ++ (resolved5 ++ (resolved6 ++ (resolved7 ++ (resolved8 ++ (
                      resolved9 ++ (resolved10 ++ (resolved11 ++ (resolved12 ++ (resolved13 ++ (
                                resolved14 ++ (resolved15 ++ (resolved16 ++
                                    (resolved17 ++ (resolved18 ++ (resolved19))))))))))))))))) :=
  resolveScopePart_append resolved_3 resolved_tail_4

private theorem resolved_tail_2 :
    resolveScopePart (resolveScopes rootFuel) (raw2 ++ (raw3 ++ (raw4 ++ (raw5 ++ (raw6 ++ (raw7 ++
                  (raw8 ++ (raw9 ++ (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (raw14 ++ (raw15 ++ (
                                    raw16 ++ (raw17 ++
                                      (raw18 ++ (raw19)))))))))))))))))) rootBindings "" 988 =
      .ok (resolved2 ++ (resolved3 ++ (resolved4 ++ (resolved5 ++ (resolved6 ++ (resolved7 ++ (
                      resolved8 ++ (resolved9 ++ (resolved10 ++ (resolved11 ++ (resolved12 ++ (
                                resolved13 ++ (resolved14 ++ (resolved15 ++ (resolved16 ++
                                      (resolved17 ++ (resolved18 ++ (resolved19)))))))))))))))))) :=
  resolveScopePart_append resolved_2 resolved_tail_3

private theorem resolved_tail_1 :
    resolveScopePart (resolveScopes rootFuel) (raw1 ++ (raw2 ++ (raw3 ++ (raw4 ++ (raw5 ++ (raw6 ++
                  (raw7 ++ (raw8 ++ (raw9 ++ (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (raw14 ++ (
                                    raw15 ++ (raw16 ++ (raw17 ++
                                        (raw18 ++ (raw19))))))))))))))))))) rootBindings "" 512 =
      .ok (resolved1 ++ (resolved2 ++ (resolved3 ++ (resolved4 ++ (resolved5 ++ (resolved6 ++ (
                      resolved7 ++ (resolved8 ++ (resolved9 ++ (resolved10 ++ (resolved11 ++ (
                                resolved12 ++ (resolved13 ++ (resolved14 ++ (resolved15 ++ (
                                        resolved16 ++ (resolved17 ++
                                          (resolved18 ++ (resolved19))))))))))))))))))) :=
  resolveScopePart_append resolved_1 resolved_tail_2

private theorem resolved_tail_0 :
    resolveScopePart (resolveScopes rootFuel) (raw0 ++ (raw1 ++ (raw2 ++ (raw3 ++ (raw4 ++ (raw5 ++
                  (raw6 ++ (raw7 ++ (raw8 ++ (raw9 ++ (raw10 ++ (raw11 ++ (raw12 ++ (raw13 ++ (raw14
                                    ++ (raw15 ++ (raw16 ++ (raw17 ++
                                          (raw18 ++ (raw19)))))))))))))))))))) rootBindings "" 0 =
      .ok (resolved0 ++ (resolved1 ++ (resolved2 ++ (resolved3 ++ (resolved4 ++ (resolved5 ++ (
                      resolved6 ++ (resolved7 ++ (resolved8 ++ (resolved9 ++ (resolved10 ++ (
                                resolved11 ++ (resolved12 ++ (resolved13 ++ (resolved14 ++ (
                                        resolved15 ++ (resolved16 ++ (resolved17 ++
                                            (resolved18 ++ (resolved19)))))))))))))))))))) :=
  resolveScopePart_append resolved_0 resolved_tail_1

private theorem source_resolved :
    resolveScopes (scopeDepth source.body) source.body [] "" = .ok resolved := by
  apply resolveScopes_of_part source_depth rootBindings_eq
  have h := congrArg (fun body =>
    resolveScopePart (resolveScopes rootFuel) body rootBindings "" 0 = .ok resolved)
    source_body_right
  exact Eq.mpr h resolved_tail_0

theorem prepare_eq :
    prepare Generated.TmlFa4Fwd.module.globals source =
      prepareResolved Generated.TmlFa4Fwd.module.globals source resolved :=
  prepare_of_resolved (by kernel_rfl) (by kernel_rfl) source_resolved

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
