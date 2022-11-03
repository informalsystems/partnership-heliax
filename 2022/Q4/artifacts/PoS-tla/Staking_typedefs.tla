---------------------- MODULE Staking_typedefs --------------------------------
(*
  Type definitions for the module Staking.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: ADDR = Str;

  @typeAlias: BALANCE = ADDR -> Int;

  @typeAlias: UNBONDED = <<ADDR, ADDR>> -> Set(UNBOND);

  @typeAlias: BONDED = <<ADDR, ADDR>> -> Set(BOND);

  @typeAlias: TOTALDELTAS = <<Int, ADDR>> -> Int;

  @typeAlias: TOTALUNBONDED = <<Int, ADDR>> -> Int;

  @typeAlias: SLASHES = ADDR -> Set(SLASH);

  @typeAlias: ENQUEUEDSLASHES = <<Int, ADDR>> -> Set(SLASH);

  @typeAlias: FROZEN = Int -> Set(ADDR);

  @typeAlias: MISBEHAVING = ADDR -> Int;


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
    lastTx: TX,
    balanceOf: BALANCE,
    unbonded: UNBONDED,
    bonded: BONDED,
    totalDeltas: TOTALDELTAS,
    totalUnbonded: TOTALUNBONDED,
    posAccount: Int,
    slashPool: Int,
    slashes: SLASHES,
    enqueuedSlashes: ENQUEUEDSLASHES,
    frozenValidators: FROZEN,
    misbehavingValidators: MISBEHAVING,
    lastTx: TX,
    nextTxId: Int,
    txCounter: Int,
    epoch: Int,
    idBonds: Int,
    idUnbonds: Int,
    idSlashes: Int,
    failed: Bool
  ];

  @typeAlias: BOND = [
    id: Int,
    amount: Int,
    start: Int,
    end: Int
  ];

  @typeAlias: UNBOND = [
    id: Int,
    amount: Int,
    start: Int,
    end: Int
  ];

  @typeAlias: SLASH = [
    id: Int,
    epoch: Int,
    stake: Int,
    typeRate: Int,
    finalRate: Int
  ];

  Below is a dummy definition to introduce the above type aliases.
 *) 
Staking_typedefs == TRUE
===============================================================================
