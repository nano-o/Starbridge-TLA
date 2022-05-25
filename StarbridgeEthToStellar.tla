------------------------------ MODULE StarbridgeEthToStellar ------------------------------

EXTENDS Integers

\* @typeAlias: STELLAR_TX = [from : STELLAR_ACCNT, to : STELLAR_ACCNT, amount : Int, seq : Int, maxTime : Int];
\* @typeAlias: ETH_TX = [from : ETH_ACCNT, to : ETH_ACCNT, amount : Int, h : HASH];

StellarAccountId == {"1_OF_STELLAR_ACCNT","2_OF_STELLAR_ACCNT"}
EthereumAccountId == {"1_OF_ETH_ACCNT","2_OF_ETH_ACCNT"}
Amount == 0..2
SeqNum == 0..2
Time == 0..2
Hash == {"0_OF_HASH","1_OF_HASH","2_OF_HASH"}

VARIABLES
    \* @type: STELLAR_ACCNT -> Int;
    stellarBalance,
    \* @type: STELLAR_ACCNT -> Int;
    stellarSeqNum,
    \* @type: Int;
    stellarTime,
    \* @type: Set(STELLAR_TX);
    stellarMempool,
    \* @type: Set(STELLAR_TX);
    stellarExecuted,
    \* @type: ETH_ACCNT -> Int;
    ethereumBalance,
    \* @type: Set(ETH_TX);
    ethereumMempool,
    \* @type: Set(ETH_TX);
    ethereumExecuted,
    \* @type: Set(HASH);
    ethereumUsedHashes,
    \* @type: HASH -> Bool;
    bridgeHasLastTx,
    \* @type: HASH -> STELLAR_TX;
    bridgeLastTx,
    \* @type: Int;
    bridgeStellarLedgerTime,
    \* @type: STELLAR_ACCNT -> Int;
    bridgeStellarSeqNum

Stellar == INSTANCE Stellar WITH
    AccountId <- StellarAccountId,
    balance <- stellarBalance,
    seqNum <- stellarSeqNum,
    time <- stellarTime,
    mempool <- stellarMempool,
    executed <- stellarExecuted

Ethereum == INSTANCE Ethereum WITH
    AccountId <- EthereumAccountId,
    balance <- ethereumBalance,
    mempool <- ethereumMempool,
    executed <- ethereumExecuted,
    usedHashes <- ethereumUsedHashes

Bridge == INSTANCE Bridge WITH
    EthereumTransaction <- Ethereum!Transaction,
    StellarTransaction <- Stellar!Transaction,
    hasLastTx <- bridgeHasLastTx,
    lastTx <- bridgeLastTx,
    stellarLedgerTime <- bridgeStellarLedgerTime,
    stellarSeqNum <- bridgeStellarSeqNum

Init == Stellar!Init /\ Ethereum!Init /\ Bridge!Init

=============================================================================
