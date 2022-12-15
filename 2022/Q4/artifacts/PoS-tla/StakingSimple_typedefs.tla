---------------------- MODULE StakingSimple_typedefs --------------------------------
(*
  Type definitions for the module Staking.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: ADDR = Str;

  @typeAlias: BALANCE = ADDR -> Int;

  @typeAlias: UNBONDED = ADDR -> Set(UNBOND);

  @typeAlias: BONDED = ADDR -> Set(BOND);

  @typeAlias: TOTALDELTAS = Int -> Int;

  @typeAlias: TOTALUNBONDED = Int -> Int;

  @typeAlias: TOTALBONDED = ADDR -> Int;

  @typeAlias: SLASHES = Seq(SLASH);

  @typeAlias: ENQUEUEDSLASHES = Int -> Int;

  @typeAlias: FROZEN = Int -> Bool;

  A transaction (a la discriminated union but all fields are packed together):
  @typeAlias: TX = [
    tag: Str,
    sender: ADDR,
    value: Int
  ];

  A state of the state machine:
  @typeAlias: STATE = [
    lastTx: TX,
    balanceOf: BALANCE,
    bonded: BONDED,
    unbonded: UNBONDED,
    totalDeltas: TOTALDELTAS,
    totalUnbonded: TOTALUNBONDED,
    totalBonded: TOTALBONDED,
    posAccount: Int,
    slashPool: Int,
    slashes: SLASHES,
    enqueuedSlashes: ENQUEUEDSLASHES,
    isFrozen: FROZEN,
    lastMisbehavingEpoch: Int,
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
