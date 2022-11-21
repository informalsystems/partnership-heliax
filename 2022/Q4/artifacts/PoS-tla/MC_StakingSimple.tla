--------------------------- MODULE MC_StakingSimple ---------------------------------
\* an instance for model checking Staking.tla with Apalache
EXTENDS Sequences, StakingSimple_typedefs

\* Use the set of four addresses, including two validators.
UserAddrs == { "user2", "user3", "val1", "val2"}

\* Set of two validators.
ValidatorAddrs == {"val1", "val2"}

PipelineLength == 1

UnbondingLength == 1

\* Should at least be UnbondingLength
MisbehavingWindow == UnbondingLength

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

\* Variables that model transactions, not the state machine.
VARIABLES    
    \* The last executed transaction.
    \*
    \* @type: TX;
    lastTx,
    \* A serial number used to identify epochs
    \* @type: Int;
    epoch

\* instantiate the spec
INSTANCE StakingSimple

\* invariants to check and break the system

\* No successful withdrawing. Use it to produce a counterexample.
NoSuccessfulWithdraw ==
    LET Example ==
        /\ lastTx.tag = "withdraw"
        /\ lastTx.value > 0
        /\ ~lastTx.fail
    IN
    ~Example

\* No withdrawing. Use it to produce a counterexample.
NoWithdraw ==
    LET Example ==
        /\ lastTx.tag = "withdraw"
        /\ ~lastTx.fail
    IN
    ~Example

\* No evidence. Use it to produce a counterexample.
NoEvidence ==
    LET Example ==
        /\ lastTx.tag = "evidence"
        /\ ~lastTx.fail
    IN
    ~Example

(* 
* It generates a trace with high coverage.
*
* Use it with:
* UserAddrs == { "user2", "user3", "val1", "val2"}
* ValidatorAddrs == {"val1", "val2"}
* PipelineLength == 1
* UnbondingLength == 1
*
*)
\* @type: Seq(STATE) => Bool;
HighCoverage(trace) ==
    \* trace[1] is the initial state
    LET state1 == trace[2] IN
    LET state2 == trace[3] IN
    LET state3 == trace[4] IN
    LET state4 == trace[5] IN
    LET state5 == trace[6] IN
    LET state6 == trace[7] IN
    LET Example ==
        \* epoch 2
        /\ state1.lastTx.tag = "unbond"
        /\ state1.lastTx.sender = "val1"
        /\ state1.lastTx.toAddr = "val1"
        /\ state1.lastTx.value > 0
        /\ ~state1.lastTx.fail
        /\ state2.lastTx.tag = "endOfEpoch"
        \* epoch 3
        /\ state3.lastTx.tag = "evidence"
        /\ state3.lastTx.sender = "val1"
        \* at initial epoch
        /\ state3.lastTx.value = 2
        /\ ~state3.lastTx.fail
        /\ state4.lastTx.tag = "delegate"
        /\ state4.lastTx.sender = "user2"
        /\ state4.lastTx.toAddr = "val2"
        /\ ~state4.lastTx.fail
        \* the evidence is processed
        /\ state5.lastTx.tag = "endOfEpoch"
        \* epoch 4
        \* tokens ready to be withdrawn
        /\ state6.lastTx.tag = "withdraw"
        /\ state6.lastTx.sender = "val1"
        /\ state6.lastTx.toAddr = "val1"
        /\ ~state6.lastTx.fail
    IN
    ~Example

\* Model invariants

\* Auxiliary functions for the model invariants

TotalBonds(sender, validator) == LET 
                                 \* @type: (Int, BOND) => Int;
                                 F(total, bond) == total + bond.amount
                                 IN ApaFoldSet(F, 0, bonded[sender, validator])

(* 
 * The sum of individual bonds is equal to totalBonded
*)

TotalBondsEquality ==
    \A user \in UserAddrs, val \in ValidatorAddrs: TotalBonds(user, val) = totalBonded[user, val]

\* PoS invariants

(* 
 * From Chris:
 * Try to capture that for a group of validators with total voting power X at
 * a particular height, the proof-of-stake model provides the ability to look up
 * bonds contributing to that voting power (for the unbonding period) and slash
 * a proportional amount of stake to X (subject to limitations e.g. repeated infractions)
 *
 * We can break this into two properties:
 *  (i) Given a validator with total voting power X at a particular height, the 
 *      proof-of-stake model provides the ability to look up bonds contributing to
 *      that voting power.
 * (ii) If evidence is found in time and there are no repeated infractions within 
 *      an epoch window, then the proof-of-stake model guarantees slashing.
 *
 * Invariant #6 verifies property (i) for the case in which there is no slashing.
 * This is the only case in which we have totalDeltas = bonds.
 *
 * Invariant #2 verifies property (ii).
*)

(*
 * Invariant #1
 * The users' balance is always greater or equal to zero
*)

BalanceAlwaysPositive == 
    \A user \in UserAddrs: balanceOf[user] >= 0


(* 
 * Invariant #2
 * posAccount is always greater or equal to zero
 *
 * This implies the following:
 * Assume that a validator misbehaves at epoch e and that evidence is found at an epoch e’ <= e + unbonding_length.
 * Assume also that the validator only misbehaves once. Then, any user whose bonds (including the validators self-bonds)
 * were contributing to the misbehaving validator's voting power are slashed when withdrawing any of those bonds.
 *
 * The logic is the following:
 * When we slash a validator (reduce its voting power) at the end of an epoch, we move tokens from the posAccount to
 * the slashPool. Thus, in the posAccount, we only have the bonded tokens that are withdrawable: this means, the bonded
 * tokens minus the slashsable amount. If a user is able to withdraw tokens that were contributing to the voting 
 * power of the misbehaving validator, then in a execution were all tokens are withdrawn, the posAccount should go
 * negative.
*)

PoSAccountAlwaysPositive == 
    posAccount >= 0

\* Auxiliary functions for Invariant #3.

foldBonds == LET
             \* @type: (Set(BOND), <<ADDR, ADDR>>) => Set(BOND);   
             F(set, pair) == set \union bonded[pair[1], pair[2]]
             IN ApaFoldSet(F, {}, UserAddrs \X ValidatorAddrs)

foldUnbonds == LET
               \* @type: (Set(UNBOND), <<ADDR, ADDR>>) => Set(UNBOND);   
               F(set, pair) == set \union unbonded[pair[1], pair[2]]
               IN ApaFoldSet(F, {}, UserAddrs \X ValidatorAddrs)

(* 
 * Invariant #3
 * First bullet from https://github.com/informalsystems/partnership-heliax/issues/25
 *
 * The amount that is self-bonded and delegated tokens is exactly equal to the amount that can be withdrawn back from PoS.
 * In other words, if all the bonds are withdrawn, the PoS balance must be equal to zero.
*)

posAccountZero ==
    foldBonds = {} /\ foldUnbonds = {} => posAccount = 0

\* Auxiliary functions for Invariants #4, #5 and #6.            

TotalSumBonds(val) == LET F(sum, user) == sum + totalBonded[user, val]
                      IN ApaFoldSet(F, 0, UserAddrs)

(* 
 * Invariant #4
 * The validator's voting power at a given epoch is greater or equal to the total amount of
 * tokens delegated to that validator.
*)

VotingpowerDelagations ==
    \A val \in ValidatorAddrs:
    TotalSumBonds(val) >= totalDeltas[UnbondingLength+PipelineLength, val]

(*
 * Invariant #5
 * The validator's voting power at a given epoch is not equal to the total amount of
 * tokens delegated to that validator due to slashing.
 * The follwoing invariant is used to create a counterexample.
*)

VotingpowerNotEqualDelagations ==
    \A val \in ValidatorAddrs:
    TotalSumBonds(val) = totalDeltas[UnbondingLength+PipelineLength, val]

(* 
 * Invariant #6
 * Disregarding slashing, the validator's voting power at a given epoch is equal to the total amount of
 * tokens delegated to that validator.
*)

VotingpowerDelagationsNoSlashing ==
    slashPool = 0 => \A val \in ValidatorAddrs: TotalSumBonds(val) = totalDeltas[UnbondingLength+PipelineLength, val]

(* 
 * Invariant #7
 * The total amount of tokens is constant.
*)

TotalAccounts == LET F(sum, user) == sum + balanceOf[user]
                 IN ApaFoldSet(F, 0, UserAddrs)

TotalAmountTokensConstant ==
    TotalAccounts + posAccount + slashPool = Cardinality(UserAddrs) * INITIAL_SUPPLY

(* 
 * Invariant #8
 * Total deltas greater or equal to zero.
*)

TotalDeltasGreater ==
    \A val \in ValidatorAddrs: totalDeltas[UnbondingLength, val] >= 0

===============================================================================