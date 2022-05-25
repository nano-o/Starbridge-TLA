------------------------------ MODULE Bridge ------------------------------

EXTENDS Integers

CONSTANTS
    StellarAccountId,
    EthereumAccountId,
    Amount,
    Hash,
    Time,
    SeqNum,
    EthereumTransaction,
    StellarTransaction

VARIABLES
    hasLastTx,
    lastTx, \* for each hash (of a tx on Ethereum), the last pre-signed tx (for Stellar) issued by the bridge
    stellarLedgerTime,
    stellarSeqNum

Init ==
    /\  hasLastTx = [h \in Hash |-> FALSE]
    /\  lastTx = [h \in Hash |-> CHOOSE tx \in StellarTransaction : TRUE]
    /\  stellarLedgerTime = 0
    /\  stellarSeqNum = [a \in StellarAccountId |-> 0]

TypeOkay ==
    /\  hasLastTx \in [Hash -> BOOLEAN]
    /\  lastTx \in [Hash -> StellarTransaction]
    /\  stellarLedgerTime \in Time
    /\  stellarSeqNum \in [StellarAccountId -> SeqNum]

Next == UNCHANGED <<lastTx, stellarLedgerTime, stellarSeqNum>>

=============================================================================
