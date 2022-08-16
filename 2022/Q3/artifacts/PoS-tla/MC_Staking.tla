--------------------------- MODULE MC_Staking ---------------------------------
\* an instance for model checking Staking.tla with Apalache
EXTENDS Sequences, Staking_typedefs

\* Use the set of four addresses, including two validators.
UserAddrs == { "user2", "user3", "val1", "val2"}

\* Set of two validators.
ValidatorAddrs == {"val1", "val2"}

PipelineLength == 2

UnbondingLength == 4

TxsEpoch == 2

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
    \* Set of jailed validators
    \*
    \* @type: Set(ADDR);
    jailedValidators,
    \* Set of frozen validators
    \*
    \* @type: Set(ADDR);
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

\* a counterexample to this invariant will produce five transactions,
NoFiveTransactions ==
    nextTxId < 5 \/ failed

\* a counterexample to this invariant will produce ten transactions,
NoTenTransactions ==
    nextTxId < 10 \/ failed

\* No withdrawing. Use it to produce a counterexample.
NoWithdraw ==
    lastTx.tag /= "withdraw"

\* From Chris
\* Try to capture that for a group of validators with total voting power X at
\* a particular height, the proof-of-stake model provides the ability to look up
\* bonds contributing to that voting power (for the unbonding period) and slash
\* a proportional amount of stake to X (subject to limitations e.g. repeated infractions)

\* Invariant #1
\* the validator's voting power at a given epoch is equal to the total amount of
\* tokens delegated to that validator

(* ValDelegatedFold(set, val) == LET SumDelegated(p,q) == p + delegated[1, q, val]
                              IN ApaFoldSet( SumDelegated, 0, set )

VotingpowerDelagations ==
    \A val \in ValidatorAddrs:
    ValDelegatedFold(UserAddrs, val) = bonded[1, val] *)

\* Invariant #2
\* the user balance is always greater or equal to zero

BalanceAlwaysPositive == 
    \A user \in UserAddrs: balanceOf[user] >= 0


\* Invariant #3
\* posAccount is always greater or equal to zero

PoSAccountAlwaysPositive == 
    posAccount >= 0

===============================================================================
