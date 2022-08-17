------------------------- MODULE Staking ---------------------------------
(*
 * Modeling the Anoma's PoS module.
 *
 * Simplifications:
 *   - Withdraws take a validator as argument
 *   - Rewards and unjailing are not specified
 *   - Each validator can misbehave at most once per execution
 * 
 * Manuel Bravo, 2022
 *)
EXTENDS Integers, Apalache, FiniteSets, Staking_typedefs

CONSTANTS
    \* Set of all user addresses.
    \* @type: Set(ADDR);
    UserAddrs,

    \* Set of all validator addresses.
    \* ValidatorAddrs must be a subset of UserAddrs
    \* @type: Set(ADDR);
    ValidatorAddrs,

    \* @type: Int;
    PipelineLength,

    \* @type: Int;
    UnbondingLength,
    
    \* tx per epoch
    \* @type: Int;
    TxsEpoch

VARIABLES
    \* Token balance for every account.
    \*
    \* @type: BALANCE;
    balanceOf,
    \* Balance of unbonded tokens that cannot be used during the bonding period.
    \*
    \* @type: UNBONDED;
    unbonded,
    \* Tokens that are delegated to a validator.
    \*
    \* @type: BONDED;
    bonded,
    \* Stake at a given validator.
    \*
    \* @type: TOTALDELTAS;
    totalDeltas,
    \* PoS special account
    \*
    \* @type: Int;
    posAccount,
    \* Slashes
    \*
    \* @type: SLASHES;
    slashes,
    \* Enqueued slashes
    \*
    \* @type: ENQUEUEDSLASHES;
    enqueuedSlashes,
    \* Set of frozen validators
    \*
    \* @type: FROZEN;
    frozenValidators


\* Variables that model transactions, epochs and offsets, not the state machine.
VARIABLES    
    \* The last executed transaction.
    \*
    \* @type: TX;
    lastTx,
    \* A serial number to assign unique ids to transactions
    \* @type: Int;
    nextTxId,
    \* Counts the transactions executed within an epoch
    \* @type: Int;
    txCounter,
    \* A serial number used to identify epochs
    \* @type: Int;
    epoch,
    \* A serial number used to identify bonds
    \* @type: Int;
    idBonds,
    \* A serial number used to identify unbonds
    \* @type: Int;
    idUnbonds,
    \* A serial number used to identify slashes
    \* @type: Int;
    idSlashes,
    \* Whether at least one transaction has failed
    \* @type: Bool;
    failed

\* the maximum value
MAX_UINT == 2^(256 - 60) - 1

\* 1 billion tokens in the initial supply
INITIAL_SUPPLY == 10^(9+18)

\* the number of tokens the validator has staked
\* @type: () => Int;
INIT_VALIDATOR_STAKE == 1000000000000000000000

\* the amount of voting power per token
SLASH_RATE == 1

\* Initialize the balances
Init ==
    /\ balanceOf = [ a \in UserAddrs |-> 
                     IF a \in ValidatorAddrs
                     THEN INITIAL_SUPPLY - INIT_VALIDATOR_STAKE
                     ELSE INITIAL_SUPPLY
                   ]
    /\ unbonded = [ a \in UserAddrs, b \in ValidatorAddrs |-> {} ]
    /\ bonded = [ a \in UserAddrs, b \in ValidatorAddrs |->
                  IF a \in ValidatorAddrs /\ a = b
                  THEN { [ id |-> 0, epoch |-> 1, amount |-> INIT_VALIDATOR_STAKE ] }
                  ELSE {}
                ]
    /\ totalDeltas = [ n \in 0..2*UnbondingLength, a \in ValidatorAddrs |-> INIT_VALIDATOR_STAKE ]
    /\ slashes = [ b \in ValidatorAddrs |-> {} ]
    /\ enqueuedSlashes = [ n \in -1..UnbondingLength, a \in ValidatorAddrs |-> {}] 
    /\ frozenValidators = [ n \in 0..UnbondingLength |-> {} ]
    /\ posAccount = Cardinality(ValidatorAddrs) * INIT_VALIDATOR_STAKE
    /\ nextTxId = 0
    /\ epoch = UnbondingLength + 1
    /\ txCounter = 0
    /\ idBonds = 1
    /\ idUnbonds = 1
    /\ idSlashes = 1
    /\ lastTx = [ id |-> 0, tag |-> "None", fail |-> FALSE ]
    /\ failed = FALSE

\* delegate `amount` tokens to a validator
Delegate(sender, validator, amount) ==
    LET fail ==
        \/ amount < 0
        \/ amount > balanceOf[sender]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "delegate", fail |-> fail,
                   sender |-> sender, toAddr |-> validator, value |-> amount ]
    /\ failed' = (fail \/ failed)
    /\ nextTxId' = nextTxId + 1
    /\ txCounter' = txCounter + 1
    /\ UNCHANGED <<epoch, unbonded, idUnbonds, slashes, idSlashes, enqueuedSlashes, frozenValidators>>
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, posAccount, bonded, idBonds, totalDeltas>>
        ELSE
          \* transaction succeeds
          \* update the balance of 'sender'
          /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ - amount]
          /\ posAccount' = posAccount + amount
          /\ bonded' = [ bonded EXCEPT ![sender, validator] = @ \union {[ id |-> idBonds,
                                                                          epoch |-> epoch + PipelineLength,
                                                                          amount |-> amount ]}]
          /\ idBonds' = idBonds + 1
          \* updates totalDeltas from PipelineLength to UnbondingLength 
          /\ totalDeltas' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> 
                              IF n >= UnbondingLength + PipelineLength /\ val = validator
                              THEN totalDeltas[n, val] + amount
                              ELSE totalDeltas[n, val]
                            ]

\* Follows the specification: it counts all bonds, even those that have not been materialized yet.
\* PAY ATTENTION TO IT
\* @type: (ADDR, ADDR) => Int;
TotalBonds(sender, validator) == LET 
                                 \* @type: (Int, BOND) => Int;
                                 F(total, bond) == total + bond.amount
                                 IN ApaFoldSet(F, 0, bonded[sender, validator])

\* @type: (Set(BOND), Int, Int) => [ remaining: Int, set: Set(UNBOND), id: Int ];
ComputedUnbonds(setBonds, amount, e) == LET 
                                         \* @type: ([ remaining: Int, set: Set(UNBOND), id: Int ], BOND) => [ remaining: Int, set: Set(UNBOND), id: Int ];
                                         F(record, bond) == 
                                         IF record.remaining > 0
                                         THEN 
                                          IF record.remaining > amount
                                          THEN [ remaining |-> record.remaining - amount,
                                                 set |-> record.set \union {[id |-> record.id, amount |-> bond.amount, start |-> bond.epoch, end |-> e]},
                                                 id |-> record.id + 1 ]
                                          ELSE [ remaining |-> 0,
                                                 set |-> record.set \union {[id |-> record.id, amount |-> record.remaining, start |-> bond.epoch, end |-> e]},
                                                 id |-> record.id + 1 ]    
                                         ELSE [ remaining |-> 0,
                                                set |-> record.set,
                                                id |-> record.id ]
                                        IN ApaFoldSet(F, [ remaining |-> amount, set |-> {}, id |-> idUnbonds], setBonds)

\* Unbond `amount` tokens from a validator
Unbond(sender, validator, amount) ==
    LET fail ==
        \/ amount < 0
        \/ TotalBonds(sender, validator) < amount
        \/ validator \in frozenValidators[0]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "unbond", fail |-> fail,
                   sender |-> sender, toAddr |-> validator, value |-> amount ]
    /\ failed' = (fail \/ failed)
    /\ nextTxId' = nextTxId + 1
    /\ txCounter' = txCounter + 1
    /\ UNCHANGED <<epoch, balanceOf, posAccount, slashes, idSlashes, enqueuedSlashes, frozenValidators>>
    /\  IF fail
        THEN
          UNCHANGED <<unbonded, idUnbonds, bonded, idBonds, totalDeltas>>
        ELSE
          LET newUnbonds == ComputedUnbonds(bonded[sender, validator], amount, epoch + UnbondingLength)
          IN
          /\ unbonded' = [ unbonded EXCEPT ![sender, validator] = @ \union newUnbonds.set ]
          /\ idUnbonds' = newUnbonds.id
          /\ bonded' = [ bonded EXCEPT ! [sender, validator] = @ \union {[ id |-> idBonds, epoch |-> epoch + UnbondingLength, amount |-> -1*amount ]}]
          /\ idBonds' = idBonds + 1
          /\ totalDeltas' = [ totalDeltas EXCEPT ![UnbondingLength*2, validator] = @ - amount]

(*
* For a given unbond, it computes the amount to be withdraw after applying a set of slashes.
*)
\* @type: (Set(SLASH), UNBOND) => Int;
ApplySlashes(setSlashes, unbond) == 
    LET 
    \* @type: (Int, SLASH) => Int;
    F(total, slash) == total - unbond.amount*slash.finalRate
    IN ApaFoldSet(F, unbond.amount, setSlashes)

(*
* Iterates over the set of unbonds for a given validator and user, and computes the total amount
* that can be withdrawn. 
*)
\* @type: (Set(UNBOND), ADDR, ADDR) => Int;
ComputeSlashableAmount(setUnbonds, sender, validator) == LET F(total, unbond) == total + ApplySlashes({ slash \in slashes[validator]: slash.epoch >= unbond.start /\ slash.epoch <= unbond.end}, unbond)
                                                         IN ApaFoldSet(F, 0, setUnbonds)

\* Withdraw unbonded tokens
Withdraw(sender, validator) ==
    LET setUnbonds == { unbond \in unbonded[sender, validator]: unbond.end <= epoch }
    IN
     LET amountAfterSlashing == ComputeSlashableAmount(setUnbonds, sender, validator)
     IN
     /\ lastTx' = [ id |-> nextTxId, tag |-> "withdraw", fail |-> FALSE,
                   sender |-> sender, toAddr |-> validator, value |-> amountAfterSlashing ]
     /\ nextTxId' = nextTxId + 1
     /\ txCounter' = txCounter + 1
     \* transaction always succeeds
     /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ + amountAfterSlashing]
     /\ posAccount' = posAccount - amountAfterSlashing
     /\ unbonded' = [ unbonded EXCEPT ![sender, validator] = @ \ setUnbonds ]
     /\ UNCHANGED  <<epoch, totalDeltas, bonded, idBonds, idUnbonds, slashes, idSlashes, enqueuedSlashes, frozenValidators, failed>>

(*
* Computes the index of TotalDeltas given an epoch e.
*)
EpochToIndexTotalDeltas(e) == UnbondingLength - (epoch - e)

(*
* When a validator misbehaves at an epoch e:
* 1. It schedules the evidence to be processed at e + UnbondingLength.
*    The enqueued slash contains the stake that the validator had at e
* 2. Freeze the validator between cur_epoch and epoch + UnbondingLength.
*)
Evidence(e, validator) ==
    /\ enqueuedSlashes' = [ enqueuedSlashes EXCEPT ![e - epoch + UnbondingLength, validator] = @ \union {[id |-> idSlashes,
                                                                                                          epoch |-> e,
                                                                                                          stake |-> totalDeltas[EpochToIndexTotalDeltas(e), validator],
                                                                                                          typeRate |-> SLASH_RATE,
                                                                                                          finalRate |-> 0]} ]
    /\ idSlashes' = idSlashes + 1
    /\ frozenValidators' = [ n \in 0..UnbondingLength |-> frozenValidators[n] \union {validator} ]
    /\ lastTx' = [ id |-> nextTxId, tag |-> "evidence", fail |-> FALSE,
                   sender |-> validator, toAddr |-> validator, value |-> e ]
    /\ UNCHANGED <<epoch, balanceOf, posAccount, totalDeltas, bonded, idBonds, unbonded, idUnbonds, slashes, nextTxId, txCounter, failed>>

(*
* Computes the Max of two numbers.
*)
Max(x, y) == IF x > y THEN x ELSE y

(*
* Computes the Min of two numbers.
*)
Min(x, y) == IF x < y THEN x ELSE y

(*
* Actual function that requires Real numbers
* ComputeFinalSlashRateValidator(setSlashes) == LET F(total, slash) == total + slash.stake * slash.typeRate
                                                IN 
                                                 LET VotingPowerFraction == ApaFoldSet(F, 0, setSlashes)
                                                 IN Min(0.01, Max(1, VotingPowerFraction*VotingPowerFraction*9))
*)

ComputeFinalSlashRateValidator(setSlashes) == 1                                          

(*
* ANTIPATTERN VARIANT
* ComputeFinalSlashRates == LET F(list, val) ==
*                            IF enqueuedSlashes[1, val] = {}
*                            THEN list
*                            ELSE [ list EXCEPT ![val] = ComputeFinalSlashRateValidator(enqueuedSlashes[0, val] \union enqueuedSlashes[1, val] \union enqueuedSlashes[2, val]) ]
*                           IN ApaFoldSet(F, [ val \in ValidatorAddrs |-> -1 ], ValidatorAddrs)
*)

ComputeFinalSlashRates == [ val \in ValidatorAddrs |->
                            IF enqueuedSlashes[0, val] = {}
                            THEN -1
                            ELSE ComputeFinalSlashRateValidator(enqueuedSlashes[-1, val] \union enqueuedSlashes[0, val] \union enqueuedSlashes[1, val])
                          ]


\* @type: (ADDR, Int, Set(SLASH)) => Int;
AccumulateSlashes(val, rate, setSlashes) == LET
                                             \* @type: (Int, SLASH) => Int;
                                             F(total, slash) == total + slash.stake * rate
                                            IN ApaFoldSet(F, 0, setSlashes)


(*
* For a set of enqueued slashes, it assigns it its final rate.
*)
\* @type: (Set(SLASH), Int) => Set(SLASH);
CreateSlashes(setSlashes, rate) == {} \union { [slash EXCEPT !.finalRate = rate]: slash \in setSlashes }

(*
* ANTIPATTERN VARIANT
* CreateSlashes(setSlashes, rate) == LET F(set, slash) == set \union { [slash EXCEPT !.finalRate = rate] }
*                                    IN ApaFoldSet(F, {}, setSlashes)
*)

(*
* At the end of an epoch e:
* 1. We compute the final slash rates. For each validator with enqueued slashes schedules
*    to be processed at e, the final rate is the same for each slash.
* 2. Shift totalDeltas applying any slash as we update the variable.
* 3. Shift enqueuedSlashes and frozenValidators.
* 4. Create slashes based on the enqueded ones.
* 5. Increment epoch.
*)
EndOfEpoch ==
    LET FinalRates == ComputeFinalSlashRates
    IN
    /\ totalDeltas' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> 
                        IF n < 2*UnbondingLength
                        THEN 
                          IF enqueuedSlashes[0, val] /= {} /\ n >= UnbondingLength + 1
                          THEN totalDeltas[n+1, val] - AccumulateSlashes(val, FinalRates[val], enqueuedSlashes[0, val])
                          ELSE totalDeltas[n+1, val]
                        ELSE 
                          IF enqueuedSlashes[0, val] /= {}
                          THEN totalDeltas[n, val] - AccumulateSlashes(val, FinalRates[val], enqueuedSlashes[0, val])
                          ELSE totalDeltas[n, val]
                      ]
    /\ enqueuedSlashes' = [ n \in -1..UnbondingLength, val \in ValidatorAddrs |-> 
                            IF n < UnbondingLength
                            THEN enqueuedSlashes[n+1, val]
                            ELSE {}
                          ]
    /\ frozenValidators' = [ n \in 0..UnbondingLength |-> 
                            IF n < UnbondingLength
                            THEN frozenValidators[n+1]
                            ELSE {}
                          ]
    /\ slashes' = [ val \in ValidatorAddrs |-> slashes[val] \union CreateSlashes(enqueuedSlashes[0, val], FinalRates[val]) ]
    /\ epoch' = epoch + 1
    /\ lastTx' = [ id |-> nextTxId, tag |-> "endOfEpoch", fail |-> FALSE,
                   sender |-> "", toAddr |-> "", value |-> epoch ]
    /\ txCounter' = 0
    /\ UNCHANGED <<balanceOf, posAccount, bonded, idBonds, unbonded, idUnbonds, idSlashes, nextTxId, failed>>

Next ==
    IF txCounter = TxsEpoch
    THEN
      \* move to the next epoch
      EndOfEpoch
    ELSE
      \E sender \in UserAddrs:
      \E validator \in ValidatorAddrs:
      \E amount \in Int:
        /\ amount <= MAX_UINT
        \* this guarantees that a validator does not misbehave more than one in an UnbondingLength period.
        /\ \/ IF validator \notin frozenValidators[0]
              THEN
                \* e is picked such that it is not in the future or too far in the past.
                \E e \in Int:
                  /\ e <= epoch
                  /\ e >= epoch - UnbondingLength
                  /\ e > 0 
                  /\ Evidence(e, validator)
              ELSE
                UNCHANGED <<epoch, totalDeltas, balanceOf, posAccount, bonded, idBonds, unbonded, idUnbonds,
                            slashes, enqueuedSlashes, idSlashes, frozenValidators, nextTxId,
                            failed, lastTx, txCounter>>
           \/ Delegate(sender, validator, amount)
           \/ Unbond(sender, validator, amount)
           \/ Withdraw(sender, validator)

\* The transition relation assuming that no failure occurs
NextNoFail ==
    Next /\ ~failed /\ ~failed'

(* False invariants to debug the spec *)


===============================================================================