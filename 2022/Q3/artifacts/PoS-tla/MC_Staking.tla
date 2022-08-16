--------------------------- MODULE MC_Staking ---------------------------------
\* an instance for model checking Staking.tla with Apalache
EXTENDS Sequences, Staking_typedefs

\* Use the set of four addresses, including two validators.
UserAddrs == { "user2", "user3", "val1", "val2"}

\* Set of two validators.
ValidatorAddrs == {"val1", "val2"}

PipelineLength == 2

UnbondingLength == 6

TxsEpoch == 4

VARIABLES
    \* Coin balance for every Cosmos account.
    \*
    \* @type: BALANCE;
    balanceOf,
    \* Balance of unbonded coins that cannot be used during the bonding period.
    \*
    \* @type: UNBONDED;
    unbonded,
    \* Coins that are delegated to Validator.
    \*
    \* @type: DELEGATED;
    delegated,
    \* Voting power of the validator.
    \*
    \* @type: BONDED;
    bonded

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
    \* Whether at least one transaction has failed
    \* @type: Bool;
    failed

\* instantiate the spec
INSTANCE Staking

\* invariants to check and break the system

\* a counterexample to this invariant will produce ten transactions,
NoTenTransactions ==
    nextTxId < 10 \/ failed

\* No withdrawing. Use it to produce a counterexample.
NoWithdraw ==
    lastTx.tag /= "withdraw"

ValDelegatedFold(set, val) == LET SumDelegated(p,q) == p + delegated[1, q, val]
                              IN ApaFoldSet( SumDelegated, 0, set )

VotingpowerDelagations ==
    \A val \in ValidatorAddrs:
    ValDelegatedFold(UserAddrs, val) = bonded[1, val]

BalanceAlwaysPositive == 
    \A user \in UserAddrs: balanceOf[user] >= 0

===============================================================================
