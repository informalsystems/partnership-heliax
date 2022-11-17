---------------------- MODULE StakingSimple_typedefs --------------------------------
(*
  Type definitions for the module Staking.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: ADDR = Str;

  @typeAlias: BALANCE = ADDR -> Int;

  @typeAlias: UNBONDED = <<ADDR, ADDR>> -> Set(UNBOND);

  @typeAlias: BONDED = <<ADDR, ADDR>> -> Set(BOND);

  @typeAlias: TOTALDELTAS = <<Int, ADDR>> -> Int;

  @typeAlias: TOTALUNBONDED = <<Int, ADDR>> -> Int;

  @typeAlias: TOTALBONDED = <<ADDR, ADDR>> -> Int;

  @typeAlias: SLASHES = ADDR -> Seq(SLASH);

  @typeAlias: ENQUEUEDSLASHES = <<Int, ADDR>> -> Int;

  @typeAlias: FROZEN = Int -> Set(ADDR);

  @typeAlias: MISBEHAVING = ADDR -> Int;


  A transaction (a la discriminated union but all fields are packed together):
  @typeAlias: TX = [
    tag: Str,
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
    totalBonded: TOTALBONDED,
    posAccount: Int,
    slashPool: Int,
    slashes: SLASHES,
    enqueuedSlashes: ENQUEUEDSLASHES,
    frozenValidators: FROZEN,
    misbehavingValidators: MISBEHAVING,
    lastTx: TX,
    epoch: Int
  ];

  @typeAlias: BOND = [
    amount: Int,
    start: Int,
    end: Int
  ];

  @typeAlias: UNBOND = [
    amount: Int,
    start: Int,
    end: Int
  ];

  @typeAlias: SLASH = [
    epoch: Int,
    stake: Int,
    finalRate: Int
  ];

  Below is a dummy definition to introduce the above type aliases.
 *) 
Staking_typedefs == TRUE
===============================================================================
