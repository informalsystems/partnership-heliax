------------------------- MODULE StakingRepeated ---------------------------------
(*
 * Anoma's PoS module.
 *
 * Simplifications:
 *   - There's a single validator
 *   - One transaction per epoch
 *   - The validator can misbehave at most once within a MisbehavingWindow
 *   - Rewards and unjailing are not specified
 * 
 * Manuel Bravo, 2022
 *)
EXTENDS Integers, Apalache, FiniteSets, Sequences, StakingRepeated_typedefs

CONSTANTS
    \* Set of all user addresses.
    \* @type: Set($addr);
    UserAddrs,

    \* Validator's name
    \* @type: $addr;
    Validator,

    \* @type: Int;
    PipelineLength,

    \* @type: Int;
    UnbondingLength,

    \* misbehaving window in epochs
    \* @type: Int;
    MisbehavingWindow

VARIABLES
    \* Token balance for every user.
    \*
    \* @type: $balance;
    balanceOf,
    \* Set of bonded tokens per user.
    \*
    \* @type: $bonded;
    bonded,
    \* Set of unbonded tokens per user.
    \*
    \* @type: $unbonded;
    unbonded,
    \* Stake of the validator at a given epoch.
    \*
    \* @type: $totalDeltas;
    totalDeltas,
    \* Stake unbonded from the validator at a given epoch.
    \*
    \* @type: $totalUnbonded;
    totalUnbonded,
    \* Total delegated per user.
    \*
    \* @type: $totalDelegated;
    totalDelegated,
    \* PoS special account
    \*
    \* @type: Int;
    posAccount,
    \* Slashed special account
    \*
    \* @type: Int;
    slashPool,
    \* Set of processed slashes
    \*
    \* @type: $slashes;
    slashes,
    \* Enqueued slash
    \*
    \* @type: $enqueuedSlashes;
    enqueuedSlashes,
    \* Determines if the validator is frozen
    \*
    \* @type: $frozen;
    isFrozen,
    \* Tracks the number of epochs the validator 
    \* has to wait before misbehaving. This is used
    \* to control how often the validator misbehave
    \*
    \* @type: Int;
    lastMisbehavingEpoch


\* Variables that model transactions and epochs, not the state machine.
VARIABLES    
    \* The last executed transaction.
    \*
    \* @type: $tx;
    lastTx,
    \* A serial number used to identify epochs
    \* cur_epoch in pseudocode
    \* @type: Int;
    epoch,
    \* @type: Int;
    counterSlashes

\* the maximum value
MAX_UINT == 2^(256 - 60) - 1

\* 1 billion tokens in the initial supply
\* INITIAL_SUPPLY == 10^(9+18)
INITIAL_SUPPLY == 20

\* the number of tokens the validator has staked initially
\* INIT_VALIDATOR_STAKE == 1000000000000000000000
INIT_VALIDATOR_STAKE == 2

\* the slash rate for any infraction
SLASH_RATE == 1

\* the set of transaction types
TRANSACTIONS == {"selfDelegate", "delegate", "selfUnbond", "unbond", "selfWithdraw", "withdraw", "evidence"}

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
                     IF a = Validator
                     THEN INITIAL_SUPPLY - INIT_VALIDATOR_STAKE
                     ELSE INITIAL_SUPPLY ]
    /\ unbonded = [ a \in UserAddrs |-> {} ]
    /\ bonded = [ a \in UserAddrs |->
                  IF a = Validator
                  THEN { [ start |-> 1, amount |-> INIT_VALIDATOR_STAKE, end |-> -1 ] }
                  ELSE {} ]
    /\ slashes =  [ a \in 0..1 |-> [ epoch |-> -1, stake |-> 0] ]
    \* Begin epoched variables
    \* range [cur_epoch-unbonding_length..cur_epoch+pipeline_length]
    /\ totalDeltas = [ n \in 0..UnbondingLength + PipelineLength |-> INIT_VALIDATOR_STAKE ]
    \* range [cur_epoch-unbonding_length..cur_epoch+pipeline_length]
    /\ totalUnbonded = [ n \in 1..UnbondingLength + PipelineLength |-> {} ]
    \* range [cur_epoch..cur_epoch+unbonding_length]
    /\ enqueuedSlashes = [ n \in 0..UnbondingLength |-> 0] 
    \* range [cur_epoch..cur_epoch+unbonding_length]
    /\ isFrozen = [ n \in 0..UnbondingLength |-> FALSE ]
    \* End epoched variables
    /\ totalDelegated = [ user \in UserAddrs |-> 
                          IF user = Validator
                          THEN INIT_VALIDATOR_STAKE
                          ELSE 0 ]
    /\ lastMisbehavingEpoch = 0
    /\ posAccount = INIT_VALIDATOR_STAKE
    /\ slashPool = 0
    /\ epoch = UnbondingLength + 1
    /\ counterSlashes = 0
    /\ lastTx = [ tag |-> "None",
                  sender |-> "",
                  value |-> 0]

\* delegate `amount` tokens to a validator
Delegate(sender, amount) ==
    /\ amount <= balanceOf[sender]
    /\ lastTx' = [ tag |-> IF sender = Validator THEN "selfDelegate" ELSE "delegate",
                   sender |-> sender,
                   value |-> amount ]
    \* update the balance of 'sender'
    /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ - amount]
    /\ posAccount' = posAccount + amount
    /\ bonded' = [ bonded EXCEPT ![sender] = @ \union {[ start |-> epoch + PipelineLength,
                                                         amount |-> amount,
                                                         end |-> -1 ]}]
    \* updates totalDeltas from PipelineLength to UnbondingLength 
    /\ totalDeltas' = [ totalDeltas EXCEPT ![UnbondingLength + PipelineLength] = @ + amount]
    /\ totalDelegated' = [ totalDelegated EXCEPT ![sender] = @ + amount]
    /\ UNCHANGED <<epoch, totalUnbonded, slashPool, unbonded, slashes, enqueuedSlashes, isFrozen, lastMisbehavingEpoch, counterSlashes>>

\* @type: (Int, Int, $slash) => Int;
BondAfterSlashing(amount, start, slash) == IF slash.epoch >= start
                                           THEN amount - amount*SLASH_RATE
                                           ELSE amount

\* @type: (Int, $addr) => { remaining: Int, bonds: Set($bond), bondToAdd: $bond, takeTotalDeltas: Int };
ComputedUnbonds(totalAmount, sender) == LET 
                                        \* @type: ({ remaining: Int, bonds: Set($bond), bondToAdd: $bond, takeTotalDeltas: Int }, $bond) => { remaining: Int, bonds: Set($bond), bondToAdd: $bond, takeTotalDeltas: Int };
                                        F(record, bond) == 
                                          IF record.remaining = 0
                                          THEN record
                                          ELSE 
                                            LET min == Min(record.remaining, bond.amount) 
                                            IN [ remaining |-> record.remaining - min,
                                                 bonds |-> record.bonds \union {bond},
                                                 bondToAdd |->
                                                   IF bond.amount = min
                                                   THEN [ amount |-> -1, start |-> bond.start, end |-> -1 ]
                                                   ELSE [ amount |-> bond.amount - min, start |-> bond.start, end |-> -1 ],
                                                 takeTotalDeltas |-> record.takeTotalDeltas + BondAfterSlashing(BondAfterSlashing(min, bond.start, slashes[0]), bond.start, slashes[1]) ]
                                        IN ApaFoldSet(F, [ remaining |-> totalAmount, bonds |-> {}, bondToAdd |-> [ amount |-> -1, start |-> -1 , end |-> -1 ], takeTotalDeltas |-> 0], bonded[sender])

\* @type: ($bond, Int, Int) => $bond;
FilterBond(bond, remain, e) == IF bond.start = e THEN [ bond EXCEPT !.amount = @ - remain ] ELSE bond

\* Unbond `amount` tokens from a validator
Unbond(sender, amount) ==
    /\ amount <= totalDelegated[sender] /\ isFrozen[0] /= TRUE
    /\ lastTx' = [ tag |-> IF sender = Validator THEN "selfUnbond" ELSE "unbond",
                   sender |-> sender,
                   value |-> amount ]
    /\ LET recordComputeUnbonds == ComputedUnbonds(amount, sender) IN
       LET unbondsToAdd == 
             IF recordComputeUnbonds.bondToAdd.amount = -1
             THEN { [ bond EXCEPT !.end = epoch + PipelineLength + UnbondingLength ] : bond \in recordComputeUnbonds.bonds }
             ELSE { FilterBond([ bond EXCEPT !.end = epoch + PipelineLength + UnbondingLength ], recordComputeUnbonds.bondToAdd.amount, recordComputeUnbonds.bondToAdd.start) : bond \in recordComputeUnbonds.bonds }
       IN
         /\ unbonded' = [ unbonded EXCEPT ![sender] = @ \union unbondsToAdd ]
         /\ bonded' = [ bonded EXCEPT ! [sender] = (@ \ recordComputeUnbonds.bonds) \union 
                        IF recordComputeUnbonds.bondToAdd.amount /= -1
                        THEN {recordComputeUnbonds.bondToAdd}
                        ELSE {} ] 
         /\ totalDeltas' = [ totalDeltas EXCEPT ![UnbondingLength + PipelineLength] = @ - recordComputeUnbonds.takeTotalDeltas]
         /\ totalUnbonded' = [ totalUnbonded EXCEPT ![UnbondingLength + PipelineLength] = unbondsToAdd ]
         /\ totalDelegated' = [ totalDelegated EXCEPT ! [sender] = @ - amount]
         /\ UNCHANGED <<epoch, balanceOf, posAccount, slashPool, slashes, enqueuedSlashes, isFrozen, lastMisbehavingEpoch, counterSlashes>>


\* @type: (Int, Int, Int, $slash) => Int;
UnbondAfterSlashing(amount, start, end, slash) == IF slash.epoch >= start /\ slash.epoch < end - UnbondingLength
                                                  THEN amount - amount*SLASH_RATE
                                                  ELSE amount

(*
* Iterates over the set of unbonds, and computes the total amount
* that can be withdrawn. 
*)
\* @type: (Set($unbond)) => Int;
ComputeAmountAfterSlashing(setUnbonds) == LET 
                                          \* @type: (Int, $unbond) => Int;
                                          F(total, unbond) == 
                                            LET AmountAfterFirstSlash == UnbondAfterSlashing(unbond.amount, unbond.start, unbond.end, slashes[0]) IN
                                            total + UnbondAfterSlashing(AmountAfterFirstSlash, unbond.start, unbond.end, slashes[1])
                                          IN ApaFoldSet(F, 0, setUnbonds)

\* Withdraw unbonded tokens
Withdraw(sender) ==
    LET setUnbonds == { unbond \in unbonded[sender]: unbond.end <= epoch } IN
    LET amountAfterSlashing == ComputeAmountAfterSlashing(setUnbonds) IN
    /\ amountAfterSlashing > 0
    /\ lastTx' = [ tag |-> IF sender = Validator THEN "selfWithdraw" ELSE "withdraw",
                   sender |-> sender,
                   value |-> amountAfterSlashing ]
    \* transaction always succeeds
    /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ + amountAfterSlashing]
    /\ posAccount' = posAccount - amountAfterSlashing
    /\ unbonded' = [ unbonded EXCEPT ![sender] = @ \ setUnbonds ]
    /\ UNCHANGED  <<epoch, totalDeltas, totalUnbonded, totalDelegated, slashPool, bonded, slashes, enqueuedSlashes, isFrozen, lastMisbehavingEpoch, counterSlashes>>

(*
* Computes the index of totalDeltas and totalUnbonded given an epoch e.
* e \in epoch-UnbondingLength..epoch, therefore EpochToIndexTotalDeltas(e) \in 0..UnbondingLength
*)
EpochToIndexTotalDeltas(e) == UnbondingLength - (epoch - e)

(*
* When a validator misbehaves at an epoch e:
* 1. It schedules the evidence to be processed at e + UnbondingLength.
*    The enqueued slash contains the stake that the validator had at e.
*    e \in epoch-UnbondingLength..epoch, therefore e - epoch + UnbondingLength \in 0..UnbondingLength
* 2. Freeze the validator between cur_epoch and epoch + UnbondingLength.
*)
Evidence(e) ==
    \* this guarantees that a validator does not misbehave more than once in MisbehavingWindow epochs
    /\ lastMisbehavingEpoch < e /\ counterSlashes < 2
    /\ enqueuedSlashes' = [ enqueuedSlashes EXCEPT ![e - epoch + UnbondingLength] = totalDeltas[EpochToIndexTotalDeltas(e)] ]
    /\ isFrozen' = [ n \in 0..UnbondingLength |-> TRUE ]
    /\ lastMisbehavingEpoch' = e + MisbehavingWindow
    /\ counterSlashes' = counterSlashes + 1
    /\ lastTx' = [ tag |-> "evidence",
                   sender |-> "",
                   value |-> e ]
    /\ UNCHANGED <<epoch, balanceOf, posAccount, slashPool, totalDeltas, totalUnbonded, totalDelegated, bonded, unbonded, slashes>>

\* @type: (Set($unbond)) => Int;
FoldUnbonds(setUnbonds) == LET 
                           \* @type: (Int, $unbond) => Int;
                           F(total, unbond) == IF unbond.start <= epoch - UnbondingLength
                                               THEN total + UnbondAfterSlashing(unbond.amount, unbond.start, epoch, slashes[0])
                                               ELSE total
                           IN ApaFoldSet(F, 0, setUnbonds)

ComputeTotalUnbonded == LET
                        \* @type: (Int -> Int, Int) => Int -> Int;
                        F(filtered, index) == [ filtered EXCEPT ![index] = FoldUnbonds({ unbond \in totalUnbonded[index] : unbond.start <= epoch - UnbondingLength }) +
                                                IF index = 1 THEN 0 ELSE filtered[index-1] ]
                        IN ApaFoldSet(F, [ n \in 1..UnbondingLength+PipelineLength |-> 0 ], 1..UnbondingLength+PipelineLength)

(*
* At the end of an epoch e:
* 1. 
*)
EndOfEpoch ==
    LET slashedTotalUnbonded == ComputeTotalUnbonded IN
    /\ IF enqueuedSlashes[0] = 0
       THEN totalDeltas' = [ n \in 0..UnbondingLength + PipelineLength |-> 
                             IF n < UnbondingLength + PipelineLength
                             THEN totalDeltas[n+1]
                             ELSE totalDeltas[n] ]
       ELSE totalDeltas' = [ n \in 0..UnbondingLength + PipelineLength |-> 
                             IF n < UnbondingLength + PipelineLength
                             THEN
                               IF n >= UnbondingLength
                               THEN totalDeltas[n+1] - (enqueuedSlashes[0] - slashedTotalUnbonded[n+1])*SLASH_RATE
                               ELSE totalDeltas[n+1]
                             ELSE totalDeltas[n] - (enqueuedSlashes[0] - slashedTotalUnbonded[n])*SLASH_RATE ]
    /\ totalUnbonded' = [ n \in 1..UnbondingLength + PipelineLength |-> 
                          IF n < UnbondingLength + PipelineLength
                          THEN totalUnbonded[n+1]
                          ELSE {} ]
    /\ enqueuedSlashes' = [ n \in 0..UnbondingLength |-> 
                            IF n < UnbondingLength
                            THEN enqueuedSlashes[n+1]
                            ELSE 0 ]
    /\ isFrozen' = [ n \in 0..UnbondingLength |-> 
                            IF n < UnbondingLength
                            THEN isFrozen[n+1]
                            ELSE FALSE ]
    /\ slashes' = IF enqueuedSlashes[0] > 0
                  THEN [ slashes EXCEPT ![counterSlashes - 1] = [ epoch |-> epoch - UnbondingLength, stake |-> enqueuedSlashes[0] ] ]
                  ELSE slashes
    /\ epoch' = epoch + 1
    /\ lastTx' = [ tag |-> "endOfEpoch",
                   sender |-> "",
                   value |-> epoch ]
    /\ posAccount' = posAccount - enqueuedSlashes[0]
    /\ slashPool' = slashPool + enqueuedSlashes[0]
    /\ UNCHANGED <<balanceOf, totalDelegated, bonded, unbonded, lastMisbehavingEpoch, counterSlashes>>

Next ==
    IF lastTx.tag \in TRANSACTIONS
    THEN
      \* move to the next epoch
      EndOfEpoch
    ELSE
      \E sender \in UserAddrs:
      \E amount \in Int:
        /\ amount > 0 /\ amount <= MAX_UINT
        \* e is picked such that it is not in the future or too far in the past.
        /\ \/ \E e \in Int: e <= epoch /\ e >= epoch - UnbondingLength /\ Evidence(e) /\ e = epoch \* only current epoch
           \/ Delegate(sender, amount)
           \/ Unbond(sender, amount)
           \/ Withdraw(sender)

(* False invariants to debug the spec *)


===============================================================================