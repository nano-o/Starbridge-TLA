------------------------------ MODULE Ethereum ------------------------------

EXTENDS Integers

CONSTANTS
    AccountId, \* the set of all account identifiers
    Amount,
    Hash

Transaction == [from : AccountId, to : AccountId, amount : Amount, hash : Hash]

VARIABLES
    balance, \* a function mapping an account id to the account's balance
    mempool, \* pending mempool; that's the interface to the outer world
    executed, \* set of executed transactions
    usedHashes

Init ==
    /\  balance \in [AccountId -> Amount]
    /\  mempool = {}
    /\  executed = {}
    /\  usedHashes = {}

ReceiveTx ==
    /\  \E a1 \in AccountId, a2 \in AccountId, x \in Amount, h \in Hash \ usedHashes :
            mempool' = mempool
                \union {[from |-> a1, to |-> a2, amount |-> x, hash |-> h]}
    /\  UNCHANGED <<balance>>

ExecuteTx == \E tx \in mempool :
    /\  tx.amount >= 0
    /\  tx.from # tx.to
    /\  tx.amount <= balance[tx.from]
    /\  balance' = [balance EXCEPT ![tx.from] = @-tx.amount, ![tx.to] = @+tx.amount]
    /\  mempool' = mempool \ {tx}
    /\  executed' = executed \union {tx}

TypeOkay ==
    /\  balance \in [AccountId -> Amount]
    /\  mempool \in SUBSET Transaction
    /\  executed \in SUBSET Transaction
    /\  usedHashes \in SUBSET Hash

=============================================================================
