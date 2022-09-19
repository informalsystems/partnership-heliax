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
* It generates a trace with high coverage
*
* Use it with UnbondingLength and PipelineLength equal to 1 and 
* UserAddrs == { "user2", "user3", "val1", "val2"}
* ValidatorAddrs == {"val1", "val2"}
* PipelineLength == 1
* UnbondingLength == 1
* TxsEpoch == 1
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

\* From Chris
\* Try to capture that for a group of validators with total voting power X at
\* a particular height, the proof-of-stake model provides the ability to look up
\* bonds contributing to that voting power (for the unbonding period) and slash
\* a proportional amount of stake to X (subject to limitations e.g. repeated infractions)

\* Invariant #1
\* the user balance is always greater or equal to zero

BalanceAlwaysPositive == 
    \A user \in UserAddrs: balanceOf[user] >= 0


\* Invariant #2
\* posAccount is always greater or equal to zero

PoSAccountAlwaysPositive == 
    posAccount >= 0

\* Invariant #3
\* the validator's voting power at a given epoch is equal to the total amount of
\* tokens delegated to that validator

SumBondsUser(user, val) == LET
                            \* @type: (Int, BOND) => Int;    
                            F(sum, bond) == sum + bond.amount
                           IN ApaFoldSet(F, 0, { b \in bonded[user, val]: b.epoch <= epoch })

TotalSumBonds(val) == LET F(sum, user) == sum + SumBondsUser(user, val)
                      IN ApaFoldSet(F, 0, UserAddrs)

VotingpowerDelagations ==
    \A val \in ValidatorAddrs:
    TotalSumBonds(val) = totalDeltas[UnbondingLength, val]

===============================================================================
