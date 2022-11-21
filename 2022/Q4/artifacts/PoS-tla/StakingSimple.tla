------------------------- MODULE StakingSimple ---------------------------------
(*
 * Modeling the Anoma's PoS module.
 *
 * Simplifications:
 *   - Withdraws take a validator as argument
 *   - Rewards and unjailing are not specified
 *   - Each validator can misbehave at most once within a MisbehavingWindow
 * 
 * Manuel Bravo, 2022
 *)
EXTENDS Integers, Apalache, FiniteSets, Sequences, StakingSimple_typedefs

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
    \* Total delegated.
    \*
    \* @type: TOTALBONDED;
    totalBonded,
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
    \* A serial number used to identify epochs
    \* cur_epoch in pseudocode
    \* @type: Int;
    epoch

\* the maximum value
MAX_UINT == 2^(256 - 60) - 1

\* 1 billion tokens in the initial supply
INITIAL_SUPPLY == 10^(9+18)

\* the number of tokens the validator has staked
\* @type: () => Int;
INIT_VALIDATOR_STAKE == 1000000000000000000000

\* the slash rate for any infraction
SLASH_RATE == 1

\* the set of transaction types
TRANSACTIONS == {"delegate", "unbond", "withdraw"}

(*
* Computes the Max of two numbers.
*)
Max(x, y) == IF x > y THEN x ELSE y

(*
* Computes the Min of two numbers.
*)
\* @type: (Int, Int) => Int;
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
                  THEN { [ start |-> 1, amount |-> INIT_VALIDATOR_STAKE, end |-> -1] }
                  ELSE {}
                ]
    /\ slashes = [ b \in ValidatorAddrs |-> << >> ]
    \* Begin epoched variables
    \* range [cur_epoch-unbonding_length..cur_epoch+unbonding_length]
    /\ totalDeltas = [ n \in 0..2*UnbondingLength, a \in ValidatorAddrs |-> INIT_VALIDATOR_STAKE ]
    \* looks like totalUnbonded does not need to be this big. It's only updated at cur_epoch+pipeline_length.
    \* range [cur_epoch-unbonding_length..cur_epoch+unbonding_length]
    /\ totalUnbonded = [ n \in 0..2*UnbondingLength, a \in ValidatorAddrs |-> 0 ]
    \* range [cur_epoch-1..cur_epoch+unbonding_length]
    /\ enqueuedSlashes = [ n \in -1..UnbondingLength, a \in ValidatorAddrs |-> 0] 
    \* range [cur_epoch..cur_epoch+unbonding_length]
    /\ frozenValidators = [ n \in 0..UnbondingLength |-> {} ]
    \* End epoched variables
    /\ totalBonded = [ user \in UserAddrs, val \in ValidatorAddrs |-> 
                       IF user = val
                       THEN INIT_VALIDATOR_STAKE
                       ELSE 0 ]
    /\ misbehavingValidators = [ val \in ValidatorAddrs |-> 0 ]
    /\ posAccount = Cardinality(ValidatorAddrs) * INIT_VALIDATOR_STAKE
    /\ slashPool = 0
    /\ epoch = UnbondingLength + 1
    /\ lastTx = [ tag |-> "None" ]

\* delegate `amount` tokens to a validator
Delegate(sender, validator, amount) ==
    /\ amount <= balanceOf[sender]
    /\ lastTx' = [ tag |-> "delegate",
                   sender |-> sender,
                   toAddr |-> validator,
                   value |-> amount ]
    \* update the balance of 'sender'
    /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ - amount]
    /\ posAccount' = posAccount + amount
    /\ bonded' = [ bonded EXCEPT ![sender, validator] = @ \union {[ start |-> epoch + PipelineLength,
                                                                    amount |-> amount,
                                                                    end |-> -1]}]
    \* updates totalDeltas from PipelineLength to UnbondingLength 
    /\ totalDeltas' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> totalDeltas[n, val] + 
                        IF n >= UnbondingLength + PipelineLength /\ val = validator
                        THEN amount
                        ELSE 0
                    ]
    /\ totalBonded' = [ totalBonded EXCEPT ![sender, validator] = @ + amount]
    /\ UNCHANGED <<epoch, totalUnbonded, slashPool, unbonded, slashes, enqueuedSlashes, frozenValidators, misbehavingValidators>>

\* @type: (ADDR, Int, Int) => Int;
BondAfterSlashing(val, amount, start) == LET
                                         \* @type: (Int, SLASH) => Int;
                                         F(total, slash) ==
                                           IF start <= slash.epoch
                                           THEN total + amount*SLASH_RATE
                                           ELSE total
                                         IN ApaFoldSeqLeft(F, 0, slashes[val])

\* @type: (Set(BOND), Int, ADDR) => [ remaining: Int, bonds: Set(BOND), bondToAdd: BOND, takeTotalDeltas: Int ];
ComputedUnbonds(setBonds, totalAmount, val) == LET 
                                               \* @type: ([ remaining: Int, bonds: Set(BOND), bondToAdd: BOND, takeTotalDeltas: Int ], BOND) => [ remaining: Int, bonds: Set(BOND), bondToAdd: BOND, takeTotalDeltas: Int ];
                                               F(record, bond) == 
                                                 IF record.remaining = 0
                                                 THEN record
                                                 ELSE 
                                                 LET min == Min(record.remaining, bond.amount) 
                                                 IN [ remaining |-> record.remaining - min,
                                                      bonds |-> record.bonds \union {[ amount |-> bond.amount, start |-> bond.start, end |-> -1]},
                                                      bondToAdd |->
                                                        IF bond.amount = min
                                                        THEN [ amount |-> -1 ]
                                                        ELSE [ amount |-> bond.amount - min, start |-> bond.start, end |-> -1 ],
                                                      takeTotalDeltas |-> record.takeTotalDeltas + min - BondAfterSlashing(val, min, bond.start) ]
                                               IN ApaFoldSet(F, [ remaining |-> totalAmount, bonds |-> {}, bondToAdd |-> [ amount |-> -1 ], takeTotalDeltas |-> 0], setBonds)

\* @type: (BOND, Int, Int) => BOND;
FilterBond(bond, remain, e) == IF bond.start = e THEN [ bond EXCEPT !.amount = @ - remain ] ELSE bond

\* Unbond `amount` tokens from a validator
Unbond(sender, validator, amount) ==
    /\ amount <= totalBonded[sender, validator] /\ validator \notin frozenValidators[0]
    /\ lastTx' = [ tag |-> "unbond",
                   sender |-> sender,
                   toAddr |-> validator,
                   value |-> amount ]
    /\ LET recordComputeUnbonds == ComputedUnbonds(bonded[sender, validator], amount, validator) IN
       LET unbondsToAdd == 
             IF recordComputeUnbonds.bondToAdd.amount = -1
             THEN { [ bond EXCEPT !.end = epoch + PipelineLength + UnbondingLength ] : bond \in recordComputeUnbonds.bonds }
             ELSE { FilterBond([ bond EXCEPT !.end = epoch + PipelineLength + UnbondingLength ], recordComputeUnbonds.bondToAdd.amount, recordComputeUnbonds.bondToAdd.start) : bond \in recordComputeUnbonds.bonds }
       IN
         /\ unbonded' = [ unbonded EXCEPT ![sender, validator] = @ \union unbondsToAdd ]
         /\ bonded' = [ bonded EXCEPT ! [sender, validator] = (@ \ recordComputeUnbonds.bonds) \union 
                        IF recordComputeUnbonds.bondToAdd.amount /= -1
                        THEN {recordComputeUnbonds.bondToAdd}
                        ELSE {} ] 
         /\ totalDeltas' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> totalDeltas[n, val] - 
                             IF n >= UnbondingLength + PipelineLength /\ val = validator
                             THEN recordComputeUnbonds.takeTotalDeltas
                             ELSE 0 ]
         /\ totalUnbonded' = [ n \in 0..2*UnbondingLength, val \in ValidatorAddrs |-> totalUnbonded[n, val] +
                               IF n >= UnbondingLength + PipelineLength /\ val = validator
                               THEN amount
                               ELSE 0 ]
         /\ totalBonded' = [ totalBonded EXCEPT ! [sender, validator] = @ - amount]
         /\ UNCHANGED <<epoch, balanceOf, posAccount, slashPool, slashes, enqueuedSlashes, frozenValidators, misbehavingValidators>>

\* @type: (Int, Seq(SLASH), Int, Int) => Int;
ProcessSlashes(amount, seqSlashes, start, end) == LET
                                                  \* @type: (Int, SLASH) => Int;
                                                  F(updatedAmount, nextSlash) ==
                                                    IF nextSlash.epoch >= start /\ nextSlash.epoch < end - UnbondingLength
                                                    THEN updatedAmount - updatedAmount*SLASH_RATE
                                                    ELSE updatedAmount
                                                  IN ApaFoldSeqLeft(F, amount, seqSlashes)

(*
* Iterates over the set of unbonds for a given validator and user, and computes the total amount
* that can be withdrawn. 
*)
\* @type: (Set(UNBOND), ADDR, ADDR) => Int;
ComputeAmountAfterSlashing(setUnbonds, sender, validator) == LET 
                                                             \* @type: (Int, UNBOND) => Int;
                                                             F(total, unbond) == total + ProcessSlashes(unbond.amount, slashes[validator], unbond.start, unbond.end)
                                                             IN ApaFoldSet(F, 0, setUnbonds)

\* Withdraw unbonded tokens
Withdraw(sender, validator) ==
    LET setUnbonds == { unbond \in unbonded[sender, validator]: unbond.end <= epoch } IN
    LET amountAfterSlashing == IF slashes[validator] = <<>> THEN 0 ELSE ComputeAmountAfterSlashing(setUnbonds, sender, validator) IN
    /\ lastTx' = [ tag |-> "withdraw",
                   sender |-> sender,
                   toAddr |-> validator,
                   value |-> amountAfterSlashing ]
    \* transaction always succeeds
    /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ + amountAfterSlashing]
    /\ posAccount' = posAccount - amountAfterSlashing
    /\ unbonded' = [ unbonded EXCEPT ![sender, validator] = @ \ setUnbonds ]
    /\ UNCHANGED  <<epoch, totalDeltas, totalUnbonded, totalBonded, slashPool, bonded, slashes, enqueuedSlashes, frozenValidators, misbehavingValidators>>

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
    \* this guarantees that a validator does not misbehave more than once in MisbehavingWindow epochs
    /\ misbehavingValidators[validator] < e
    /\ enqueuedSlashes' = [ enqueuedSlashes EXCEPT ![e - epoch + UnbondingLength, validator] = totalDeltas[EpochToIndexTotalVariables(e), validator] ]
    /\ frozenValidators' = [ n \in 0..UnbondingLength |-> frozenValidators[n] \union {validator} ]
    /\ misbehavingValidators' = [ misbehavingValidators EXCEPT ![validator] = e + MisbehavingWindow ]
    /\ lastTx' = [ tag |-> "evidence",
                   sender |-> validator,
                   toAddr |-> validator,
                   value |-> e ]
    /\ UNCHANGED <<epoch, balanceOf, posAccount, slashPool, totalDeltas, totalUnbonded, totalBonded, bonded, unbonded, slashes>>

\* @type: () => Int;
TotalSlashedAmount == LET F(total, val) == total + enqueuedSlashes[0, val]*SLASH_RATE
                      IN ApaFoldSet(F, 0, ValidatorAddrs)

(*
* At the end of an epoch e:
* 1. 
*)
EndOfEpoch ==
    LET penaltyValEpoch == [ n \in UnbondingLength+1..2*UnbondingLength, val \in ValidatorAddrs |->
                             IF enqueuedSlashes[0, val] > 0
                             THEN (enqueuedSlashes[0, val] - totalUnbonded[n, val])*SLASH_RATE
                             ELSE 0 ] IN
    LET totalSlashed == TotalSlashedAmount IN
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
                          THEN totalUnbonded[n+1, val] - totalUnbonded[0, val]
                          ELSE totalUnbonded[n, val] - totalUnbonded[0, val]
                        ]
    /\ enqueuedSlashes' = [ n \in -1..UnbondingLength, val \in ValidatorAddrs |-> 
                            IF n < UnbondingLength
                            THEN enqueuedSlashes[n+1, val]
                            ELSE 0
                          ]
    /\ frozenValidators' = [ n \in 0..UnbondingLength |-> 
                            IF n < UnbondingLength
                            THEN frozenValidators[n+1]
                            ELSE {}
                          ]
    /\ slashes' = [ val \in ValidatorAddrs |->
                    IF enqueuedSlashes[0, val] > 0
                    THEN Append(slashes[val], [ epoch |-> epoch - UnbondingLength, stake |-> enqueuedSlashes[0, val], finalRate |-> SLASH_RATE ])
                    ELSE slashes[val] ]
    /\ epoch' = epoch + 1
    /\ lastTx' = [ tag |-> "endOfEpoch",
                   sender |-> "", toAddr |-> "",
                   value |-> epoch ]
    /\ posAccount' = posAccount - totalSlashed
    /\ slashPool' = slashPool + totalSlashed
    /\ UNCHANGED <<balanceOf, totalBonded, bonded, unbonded, misbehavingValidators>>

Next ==
    IF lastTx.tag \in TRANSACTIONS
    THEN
      \* move to the next epoch
      EndOfEpoch
    ELSE
      \E sender \in UserAddrs:
      \E validator \in ValidatorAddrs:
      \E amount \in Int:
        /\ amount >= 0 /\ amount <= MAX_UINT
        \* e is picked such that it is not in the future or too far in the past.
        /\ \/ \E e \in Int: e <= epoch /\ e >= epoch - UnbondingLength /\ Evidence(e, validator)
           \/ Delegate(sender, validator, amount)
           \/ Unbond(sender, validator, amount)
           \/ Withdraw(sender, validator)

(* False invariants to debug the spec *)


===============================================================================