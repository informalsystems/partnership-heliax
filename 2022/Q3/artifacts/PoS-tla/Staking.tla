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
    TxsEpoch,

    \* misbehaving window in epochs
    \* @type: Int;
    MisbehavingWindow

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
    \* Stake unbonded from a given validator at a given epoch.
    \*
    \* @type: TOTALUNBONDED;
    totalUnbonded,
    \* PoS special account
    \*
    \* @type: Int;
    posAccount,
    \* Slashed special account
    \*
    \* @type: Int;
    slashPool,
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
    frozenValidators,
    \* Set of misbehaving validators
    \*
    \* @type: MISBEHAVING;
    misbehavingValidators


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
    \* cur_epoch in pseudocode
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

\* the slash rate for any infraction
SLASH_RATE == 1

(*
* Computes the Max of two numbers.
*)
Max(x, y) == IF x > y THEN x ELSE y

(*
* Computes the Min of two numbers.
*)
Min(x, y) == IF x < y THEN x ELSE y

\* Initialize the balances
Init ==
    /\ balanceOf = [ a \in UserAddrs |-> 
                     IF a \in ValidatorAddrs
                     THEN INITIAL_SUPPLY - INIT_VALIDATOR_STAKE
                     ELSE INITIAL_SUPPLY
                   ]
    /\ unbonded = [ a \in UserAddrs, b \in ValidatorAddrs |-> {} ]
    /\ bonded = [ a \in UserAddrs, b \in ValidatorAddrs |->
                  IF a = b
                  THEN { [ id |-> 0, start |-> 1, amount |-> INIT_VALIDATOR_STAKE, end |-> -1] }
                  ELSE {}
                ]
    /\ slashes = [ b \in ValidatorAddrs |-> {} ]
    \* Begin epoched variables
    \* range [cur_epoch-unbonding_length..cur_epoch+unbonding_length]
    /\ totalDeltas = [ n \in 0..2*UnbondingLength, a \in ValidatorAddrs |-> INIT_VALIDATOR_STAKE ]
    \* looks like totalUnbonded does not need to be this big. It's only updated at cur_epoch+pipeline_length.
    \* range [cur_epoch-unbonding_length..cur_epoch+unbonding_length]
    /\ totalUnbonded = [ n \in 0..2*UnbondingLength, a \in ValidatorAddrs |-> 0 ]
    \* range [cur_epoch-1..cur_epoch+unbonding_length]
    /\ enqueuedSlashes = [ n \in -1..UnbondingLength, a \in ValidatorAddrs |-> {}] 
    \* range [cur_epoch..cur_epoch+unbonding_length]
    /\ frozenValidators = [ n \in 0..UnbondingLength |-> {} ]
    \* End epoched variables
    /\ misbehavingValidators = [ val \in ValidatorAddrs |-> 0 ]
    /\ posAccount = Cardinality(ValidatorAddrs) * INIT_VALIDATOR_STAKE
    /\ slashPool = 0
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
    /\ UNCHANGED <<epoch, totalUnbonded, slashPool, unbonded, idUnbonds, slashes, idSlashes, enqueuedSlashes, frozenValidators, misbehavingValidators>>
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, posAccount, bonded, idBonds, totalDeltas>>
        ELSE
          \* transaction succeeds
          \* update the balance of 'sender'
          /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ - amount]
          /\ posAccount' = posAccount + amount
          /\ bonded' = [ bonded EXCEPT ![sender, validator] = @ \union {[ id |-> idBonds,
                                                                          start |-> epoch + PipelineLength,
                                                                          amount |-> amount,
                                                                          end |-> -1]}]
          /\ idBonds' = idBonds + 1
          \* updates totalDeltas from PipelineLength to UnbondingLength 
          /\ totalDeltas' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> totalDeltas[n, val] + 
                              IF n >= UnbondingLength + PipelineLength /\ val = validator
                              THEN amount
                              ELSE 0
                            ]

\* Follows the specification: it counts all bonds, even those that have not been materialized yet.
\* PAY ATTENTION TO IT
\* @type: (ADDR, ADDR) => Int;
TotalBonds(sender, validator) == LET 
                                 \* @type: (Int, BOND) => Int;
                                 F(total, bond) == total + bond.amount
                                 IN ApaFoldSet(F, 0, {b \in bonded[sender, validator]: b.end = -1})

\* @type: (Set(BOND), Int, Int) => [ remaining: Int, unbonds: Set(UNBOND), bonds: Set(BOND), modifiedBond: Set(BOND), id: Int ];
ComputedUnbonds(setBonds, totalAmount, e) == LET 
                                         \* @type: ([ remaining: Int, unbonds: Set(UNBOND), bonds: Set(BOND), modifiedBond: Set(BOND), id: Int ], BOND) => [ remaining: Int, set: Set(UNBOND), id: Int ];
                                         F(record, bond) == 
                                         IF record.remaining = 0
                                         THEN record
                                         ELSE 
                                          LET min == Min(record.remaining, bond.amount) 
                                          IN [ remaining |-> record.remaining - min,
                                               unbonds |-> record.unbonds \union {[id |-> record.id, amount |-> min, start |-> bond.start, end |-> e]},
                                               bondsToRemove |-> record.bondsToRemove \union {bond},
                                               bondsToAdd |-> record.bondsToAdd \union {[id |-> bond.id, amount |-> min, start |-> bond.start, end |-> epoch + PipelineLength]} \union
                                                IF bond.amount = min
                                                THEN {}
                                                ELSE {[id |-> idBonds, amount |-> bond.amount - min, start |-> bond.start, end |-> -1]},
                                               id |-> record.id + 1 ]
                                        IN ApaFoldSet(F, [ remaining |-> totalAmount, unbonds |-> {}, bondsToRemove |-> {}, bondsToAdd |-> {}, id |-> idUnbonds], setBonds)

\* @type: (Int, Set(SLASH)) => Int;
BondAfterSlashing(amount, setSlashes) == LET
                                         \* @type: (Int, SLASH) => Int;
                                         F(total, slash) == total + (amount - amount*slash.finalRate)
                                         IN ApaFoldSet(F, 0, setSlashes)

\* @type: (ADDR, Set(BOND)) => Int;
ComputeTakeTotalDeltas(val, setBonds) == LET
                                         \* @type: (Int, BOND) => Int;
                                         F(total, bond) == total + BondAfterSlashing(bond.amount, { slash \in slashes[val]: bond.start <= slash.epoch })
                                         IN ApaFoldSet(F, 0, setBonds)
                                

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
    /\ UNCHANGED <<epoch, balanceOf, posAccount, slashPool, slashes, idSlashes, enqueuedSlashes, frozenValidators, misbehavingValidators>>
    /\  IF fail
        THEN
          UNCHANGED <<unbonded, idUnbonds, bonded, idBonds, totalDeltas, totalUnbonded>>
        ELSE
          LET recordComputeUnbonds == ComputedUnbonds({bond \in bonded[sender, validator]: bond.end = -1}, amount, epoch + PipelineLength + UnbondingLength) IN
          LET takeTotalDeltas == ComputeTakeTotalDeltas(validator, {bond \in recordComputeUnbonds.bondsToAdd: bond.end /= -1}) IN
          /\ unbonded' = [ unbonded EXCEPT ![sender, validator] = @ \union recordComputeUnbonds.unbonds ]
          /\ idUnbonds' = recordComputeUnbonds.id
          /\ bonded' = [ bonded EXCEPT ! [sender, validator] = (@ \ recordComputeUnbonds.bondsToRemove) \union recordComputeUnbonds.bondsToAdd]
          /\ idBonds' = idBonds + 1
          /\ totalDeltas' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> totalDeltas[n, val] - 
                              IF n >= UnbondingLength + PipelineLength /\ val = validator
                              THEN takeTotalDeltas
                              ELSE 0
                            ]
          /\ totalUnbonded' = [ totalUnbonded EXCEPT ! [UnbondingLength + PipelineLength, validator] = @ + amount]
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
     /\ UNCHANGED  <<epoch, totalDeltas, totalUnbonded, slashPool, bonded, idBonds, idUnbonds, slashes, idSlashes, enqueuedSlashes, frozenValidators, misbehavingValidators, failed>>

(*
* Computes the index of totalDeltas and totalUnbonded given an epoch e.
*)
EpochToIndexTotalVariables(e) == UnbondingLength - (epoch - e)

(*
* When a validator misbehaves at an epoch e:
* 1. It schedules the evidence to be processed at e + UnbondingLength.
*    The enqueued slash contains the stake that the validator had at e
* 2. Freeze the validator between cur_epoch and epoch + UnbondingLength.
*)
Evidence(e, validator) ==
    /\ enqueuedSlashes' = [ enqueuedSlashes EXCEPT ![e - epoch + UnbondingLength, validator] = @ \union {[id |-> idSlashes,
                                                                                                          epoch |-> e,
                                                                                                          stake |-> totalDeltas[EpochToIndexTotalVariables(e), validator],
                                                                                                          typeRate |-> SLASH_RATE,
                                                                                                          finalRate |-> 0]} ]
    /\ idSlashes' = idSlashes + 1
    /\ frozenValidators' = [ n \in 0..UnbondingLength |-> frozenValidators[n] \union {validator} ]
    /\ misbehavingValidators' = [ misbehavingValidators EXCEPT ![validator] = MisbehavingWindow ]
    /\ lastTx' = [ id |-> nextTxId, tag |-> "evidence", fail |-> FALSE,
                   sender |-> validator, toAddr |-> validator, value |-> e ]
    /\ UNCHANGED <<epoch, balanceOf, posAccount, slashPool, totalDeltas, totalUnbonded, bonded, idBonds, unbonded, idUnbonds, slashes, nextTxId, txCounter, failed>>

(*
* Actual function that requires Real numbers
* FinalSlashRate(setSlashes) == LET F(total, slash) == total + slash.stake * slash.typeRate
                                IN 
                                 LET VotingPowerFraction == ApaFoldSet(F, 0, setSlashes)
                                 IN Min(0.01, Max(1, VotingPowerFraction*VotingPowerFraction*9))
*)

FinalSlashRate(setSlashes) == 1                                          

(*
* For a given validator, aggregates totalUnbonds from epoch=initEpoch up to cur_epoch
*
* pseudocode PoS-model: @@ func end_of_epoch() 
* var total_unbonded = 0
* //find the total unbonded from the slash epoch up to the current epoch first
* forall (epoch in slash.epoch..cur_epoch) do
*   total_unbonded += validators[validator_address].total_unbonded[epoch]
*)
SumUnbonded(val, initEpoch) == LET F(total, n) == total + totalUnbonded[n, val]
                               IN ApaFoldSet(F, 0, { x \in 0..UnbondingLength: initEpoch <= x /\ x <= UnbondingLength })

(*
* For a given validator with evidence to be processed at the end of cur_epoch, it computes the
* slashable amount at every epoch >= cur_epoch + 1 and epoch <= cur_epoch + unbonding_length
*
* pseudocode PoS-model: @@ func end_of_epoch() 
* var last_slash = 0
* forall (offset in 1..unbonding_length) do
*   total_unbonded += validators[validator_address].total_unbonded[cur_epoch + offset]
*   var this_slash = (total_staked - total_unbonded) * slash.rate
*   var diff_slashed_amount = last_slash - this_slash
*   last_slash = this_slash
*   update_total_deltas(validator_address, offset, diff_slashed_amount)
*)
\* @type: (Int, Int -> Int, ADDR, SLASH, Int) => [acc: Int, vector: Int -> Int];
SlashableAmountPerSlash(accInit, vectorInit, val, slash, rate) == LET
                                                                  \* @type: ([acc: Int, vector: Int -> Int], Int) => [acc: Int, vector: Int -> Int];
                                                                  F(record, n) == 
                                                                    LET sumUnbonded == record.acc + totalUnbonded[n, val]
                                                                    IN [ acc |-> sumUnbonded,
                                                                         vector |-> [ record.vector EXCEPT ![n] = @ + (slash.stake-sumUnbonded)*rate ] ]
                                                                  IN ApaFoldSet(F, [acc |-> accInit, vector |-> vectorInit], UnbondingLength+1..2*UnbondingLength)

(*
* For a given validator with evidence to be processed at the end of cur_epoch, it computes the
* slashable amount at every epoch >= cur_epoch + 1 and epoch <= cur_epoch + unbonding_length
*)
\* @type: (ADDR, Int, Set(SLASH)) => Int -> Int;
SlashableAmountForVal(val, rate, setSlashes) == LET
                                                \* @type: (Int -> Int, SLASH) => Int -> Int;
                                                F(acc, slash) ==  SlashableAmountPerSlash(SumUnbonded(val, EpochToIndexTotalVariables(slash.epoch)),
                                                                                          acc,
                                                                                          val,
                                                                                          slash,
                                                                                          rate).vector
                                                IN ApaFoldSet(F, [ n \in UnbondingLength+1..2*UnbondingLength |-> 0], setSlashes)

(*
* For all validators with evidence to be processed at the end of cur_epoch, it 
* computes the slashable amount at every epoch >= cur_epoch + 1 and epoch <= cur_epoch + unbonding_length
*)
SlashableAmountForAll == LET F(amounts, val) ==
                          LET vector == SlashableAmountForVal(val,
                                                              FinalSlashRate(enqueuedSlashes[-1, val] \union enqueuedSlashes[0, val] \union enqueuedSlashes[1, val]),
                                                              enqueuedSlashes[0, val]) 
                          IN [n \in UnbondingLength+1..2*UnbondingLength, a \in ValidatorAddrs |-> 
                               IF a = val
                               THEN vector[n]
                               ELSE amounts[n, a]
                             ]
                         IN ApaFoldSet(F, [ n \in UnbondingLength+1..2*UnbondingLength, a \in ValidatorAddrs |-> 0 ], { val \in ValidatorAddrs: enqueuedSlashes[0, val] /= {} })

(*
* For a set of enqueued slashes, it assigns it its final rate.
*)
\* @type: (Set(SLASH), Int) => Set(SLASH);
CreateSlashes(setSlashes, rate) == {} \union { [slash EXCEPT !.finalRate = rate]: slash \in setSlashes }

\* @type: (Set(SLASH)) => Int;
TotalSlashedAmountPerValidator(setSlashes) == LET 
                                              \* @type: (Int, SLASH) => Int;
                                              F(total, slash) == total + slash.stake*slash.finalRate
                                              IN ApaFoldSet(F, 0, setSlashes)
\* @type: (ADDR -> Set(SLASH)) => Int;
TotalSlashedAmount(setSlashesIndexed) == LET F(total, val) == total + TotalSlashedAmountPerValidator(setSlashesIndexed[val])
                                         IN ApaFoldSet(F, 0, ValidatorAddrs)

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
    LET penaltyValEpoch == SlashableAmountForAll IN
    LET newSlashes == [ val \in ValidatorAddrs |-> 
                        CreateSlashes(enqueuedSlashes[0, val],
                                      FinalSlashRate(enqueuedSlashes[-1, val] \union enqueuedSlashes[0, val] \union enqueuedSlashes[1, val])) ] IN
    LET totalSlashed == TotalSlashedAmount(newSlashes) IN
    /\ totalDeltas' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> 
                        IF n < 2*UnbondingLength
                        THEN
                          IF n >= UnbondingLength
                          THEN totalDeltas[n+1, val] - penaltyValEpoch[n+1, val]
                          ELSE totalDeltas[n+1, val]
                        ELSE totalDeltas[n, val] - penaltyValEpoch[n, val]
                      ]
    /\ totalUnbonded' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> 
                          IF n < 2*UnbondingLength
                          THEN totalUnbonded[n+1, val]
                          ELSE 0
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
    /\ misbehavingValidators' = [ val \in ValidatorAddrs |-> Max(0, misbehavingValidators[val]-1) ]
    /\ slashes' = [ val \in ValidatorAddrs |-> slashes[val] \union newSlashes[val]]
    /\ epoch' = epoch + 1
    /\ lastTx' = [ id |-> nextTxId, tag |-> "endOfEpoch", fail |-> FALSE,
                   sender |-> "", toAddr |-> "", value |-> epoch ]
    /\ txCounter' = 0
    /\ posAccount' = posAccount - totalSlashed
    /\ slashPool' = slashPool + totalSlashed
    /\ UNCHANGED <<balanceOf, bonded, idBonds, unbonded, idUnbonds, idSlashes, nextTxId, failed>>

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
        \* this guarantees that a validator does not misbehave more than once in MisbehavingWindow epochs
        /\ \/ IF misbehavingValidators[validator] = 0
              THEN
                \* e is picked such that it is not in the future or too far in the past.
                \E e \in Int:
                  /\ e <= epoch
                  /\ e >= epoch - UnbondingLength
                  /\ e > 0 
                  /\ Evidence(e, validator)
              ELSE
                UNCHANGED <<epoch, totalDeltas, totalUnbonded, balanceOf, posAccount, slashPool, bonded, idBonds, unbonded, idUnbonds,
                            slashes, enqueuedSlashes, idSlashes, frozenValidators, misbehavingValidators, nextTxId,
                            failed, lastTx, txCounter>>
           \/ Delegate(sender, validator, amount)
           \/ Unbond(sender, validator, amount)
           \/ Withdraw(sender, validator)

\* The transition relation assuming that no failure occurs
NextNoFail ==
    Next /\ ~failed /\ ~failed'

(* False invariants to debug the spec *)


===============================================================================