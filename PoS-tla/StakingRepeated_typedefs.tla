---------------------- MODULE StakingRepeated_typedefs --------------------------------
(*
  Type definitions for the module Staking.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: addr = Str;

  @typeAlias: balance = $addr -> Int;

  @typeAlias: unbonded = $addr -> Set($unbond);

  @typeAlias: bonded = $addr -> Set($bond);

  @typeAlias: totalDeltas = Int -> Int;

  @typeAlias: totalUnbonded = Int -> Set($unbond);

  @typeAlias: totalDelegated = $addr -> Int;

  @typeAlias: slashes = Int -> $slash;

  @typeAlias: enqueuedSlashes = Int -> Int;

  @typeAlias: frozen = Int -> Bool;

  A transaction (a la discriminated union but all fields are packed together):
  @typeAlias: tx = {
    tag: Str,
    sender: $addr,
    value: Int
  };

  @typeAlias: bond = {
    amount: Int,
    start: Int,
    end: Int
  };

  @typeAlias: unbond = {
    amount: Int,
    start: Int,
    end: Int
  };

  @typeAlias: slash = {
    epoch: Int,
    stake: Int
  };

  A state of the state machine:
  @typeAlias: state = {
    lastTx: $tx,
    balanceOf: $balance,
    bonded: $bonded,
    unbonded: $unbonded,
    totalDeltas: $totalDeltas,
    totalUnbonded: $totalUnbonded,
    totalDelegated: $totalDelegated,
    posAccount: Int,
    slashPool: Int,
    slashes: $slashes,
    enqueuedSlashes: $enqueuedSlashes,
    isFrozen: $frozen,
    lastMisbehavingEpoch: Int,
    epoch: Int,
    counterSlashes: Int
  };

  Below is a dummy definition to introduce the above type aliases.
 *) 
StakingRepeated_typedefs == TRUE
===============================================================================
