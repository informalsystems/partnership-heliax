---------------------- MODULE Staking_typedefs --------------------------------
(*
  Type definitions for the module Staking.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: ADDR = Str;

  @typeAlias: BALANCE = ADDR -> Int;

  @typeAlias: EPOCHED = <<Int, ADDR>> -> Int;

  @typeAlias: DELEGATEDEPOCHED = <<Int, ADDR, ADDR>> -> Int;

  A transaction (a la discriminated union but all fields are packed together):
  @typeAlias: TX = [
    tag: Str,
    id: Int,
    fail: Bool,
    sender: ADDR,
    toAddr: ADDR,
    value: Int
  ];

  A state of the state machine:
  @typeAlias: STATE = [
    balanceOf: BALANCE,
    delegated: DELEGATEDEPOCHED,
    unbonded: EPOCHED,
    bonded: EPOCHED,
    lastTx: TX,
    nextTxId: Int,
    failed: Bool
  ];

  Below is a dummy definition to introduce the above type aliases.
 *) 
Staking_typedefs == TRUE
===============================================================================
