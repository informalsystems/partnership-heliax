--------------------------- MODULE MC_Staking ---------------------------------
\* an instance for model checking Staking.tla with Apalache
EXTENDS Sequences, Staking_typedefs

\* Use the set of three addresses.
UserAddrs == { "user2", "user3", "validator" }

PipelineLength == 6

UnbondingLength == 2

VARIABLES
    \* Coin balance for every Cosmos account.
    \*
    \* @type: BALANCE;
    balanceOf,
    \* Balance of unbonded coins that cannot be used during the bonding period.
    \*
    \* @type: EPOCHED;
    unbonded,
    \* Coins that are delegated to Validator.
    \*
    \* @type: EPOCHED;
    delegated

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

BalanceAlwaysPositive == 
    \A user \in UserAddrs: balanceOf[user] >= 0

\* takes forever to check this
\*UserConstantAmount == 
\*    \A user \in UserAddrs: balanceOf[user] + unbonded[user] + delegated[user] = INITIAL_SUPPLY

===============================================================================
