--------------------------- MODULE MC_Staking ---------------------------------
\* an instance for model checking Staking.tla with Apalache
EXTENDS Sequences, Staking_typedefs

\* Use the set of four addresses, including two validators.
UserAddrs == { "user2", "user3", "val1", "val2"}

\* Set of two validators.
ValidatorAddrs == {"val1", "val2"}

PipelineLength == 1

UnbondingLength == 1

TxsEpoch == 1

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
    frozenValidators

\* Variables that model transactions, not the state machine.
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

\* instantiate the spec
INSTANCE Staking

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
* TxsEpoch == 1
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

\* PoS invariants

(* 
 * From Chris:
 * Try to capture that for a group of validators with total voting power X at
 * a particular height, the proof-of-stake model provides the ability to look up
 * bonds contributing to that voting power (for the unbonding period) and slash
 * a proportional amount of stake to X (subject to limitations e.g. repeated infractions)
 *
 * We can break this into two properties:
 *  (i) Given a validators with total voting power X at a particular height, the 
 *      proof-of-stake model provides the ability to look up bonds contributing to
 *      that voting power.
 * (ii) If evidence is found in time and there are no repeated infractions within 
 *      an epoch window, then the proof-of-stake model guarantees slashing.
 *
 * Invariant #6 verifies property (i) for the case in which there is no slashing.
 * This is the nly case in which we have totalDeltas = bonds.
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
 * power of the misbehaving validator, then in a execution were all toekns are withdrawn, the posAccount should go
 * negative.
*)

PoSAccountAlwaysPositive == 
    posAccount >= 0

\* Auxiliary functions for Invariant #3.

bondsWithOpenEnd == LET
                    \* @type: (Set(BOND), <<ADDR, ADDR>>) => Set(BOND);   
                    F(set, pair) == set \union { bond \in bonded[pair[1], pair[2]]: bond.end = -1 }
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
    bondsWithOpenEnd = {} /\ foldUnbonds = {} => posAccount = 0

\* Auxiliary functions for Invariants #4, #5 and #6.            

SumBondsUser(user, val) == LET
                           \* @type: (Int, BOND) => Int;    
                           F(sum, bond) == sum + bond.amount
                           IN ApaFoldSet(F, 0, { b \in bonded[user, val]:
                                                 /\ b.start <= epoch
                                                 /\ b.end /= -1 => b.end > epoch })

TotalSumBonds(val) == LET F(sum, user) == sum + SumBondsUser(user, val)
                      IN ApaFoldSet(F, 0, UserAddrs)

(* 
 * Invariant #4
 * The validator's voting power at a given epoch is greater or equal to the total amount of
 * tokens delegated to that validator.
*)

VotingpowerDelagations ==
    \A val \in ValidatorAddrs:
    TotalSumBonds(val) >= totalDeltas[UnbondingLength, val]

(*
 * Invariant #5
 * The validator's voting power at a given epoch is not equal to the total amount of
 * tokens delegated to that validator due to slashing.
 * The follwoing invariant is used to create a counterexample.
*)

VotingpowerNotEqualDelagations ==
    \A val \in ValidatorAddrs:
    TotalSumBonds(val) = totalDeltas[UnbondingLength, val]

(* 
 * Invariant #6
 * Disregarding slashing, the validator's voting power at a given epoch is equal to the total amount of
 * tokens delegated to that validator.
*)

VotingpowerDelagationsNoSlashing ==
    slashPool = 0 => \A val \in ValidatorAddrs: TotalSumBonds(val) = totalDeltas[UnbondingLength, val]

(* 
 * Invariant #7
 * The total amount of tokens is constant.
*)

TotalAccounts == LET F(sum, user) == sum + balanceOf[user]
                 IN ApaFoldSet(F, 0, UserAddrs)

TotalAmountTokensConstant ==
    TotalAccounts + posAccount + slashPool = Cardinality(UserAddrs) * INITIAL_SUPPLY
    
===============================================================================