------------------------------ MODULE StarbridgeEthToStellarInstance1 ------------------------------

EXTENDS Integers, Apalache

\* @typeAlias: STELLAR_TX = [src : STELLAR_ACCNT, from : STELLAR_ACCNT, to : STELLAR_ACCNT, amount : Int, seq : Int, maxTime : Int, depositId : HASH];
\* @typeAlias: ETH_TX = [from : ETH_ACCNT, to : ETH_ACCNT, amount : Int, stellarDst : STELLAR_ACCNT, hash : HASH, depositId : HASH];

StellarAccountId == {"BRIDGE_OF_STELLAR_ACCNT","USER_OF_STELLAR_ACCNT","USER2_OF_STELLAR_ACCNT"}
EthereumAccountId == {"BRIDGE_OF_ETH_ACCNT","USER_OF_ETH_ACCNT","USER2_OF_ETH_ACCNT"}
Amount == 1..1 \* transfer amounts
SeqNum == 0..1 \* we need at least two consecutive seqnums to be able to execute transactions on Stellar
Time == 0..0
WithdrawWindow == 1 \* time window the user has to execute a withdraw operation on Stellar
(* Hash == {"0_OF_HASH","1_OF_HASH","2_OF_HASH","3_OF_HASH"} *)
Hash == {"0_OF_HASH","1_OF_HASH","2_OF_HASH"}

BridgeStellarAccountId == "BRIDGE_OF_STELLAR_ACCNT"
BridgeEthereumAccountId == "BRIDGE_OF_ETH_ACCNT"

VARIABLES
    \* state of Stellar and Ethereum:
    \* @type: STELLAR_ACCNT -> Int;
    stellarSeqNum,
    \* @type: Int;
    stellarTime,
    \* @type: Set(STELLAR_TX);
    stellarMempool,
    \* @type: Set(STELLAR_TX);
    stellarExecuted,
    \* @type: Int -> Set(ETH_TX);
    ethereumExecuted,
    \* @type: Int;
    ethereumTime,

    \* state of the bridge:
    \* @type: Set(HASH);
    issuedWithdrawTx,
    \* @type: HASH -> STELLAR_TX;
    lastWithdrawTx, \* NOTE: this could be a partial function to avoid needing the variable above, but it's bad for Apalache's SMT encoding
    \* @type: Int;
    bridgeStellarTime,
    \* @type: STELLAR_ACCNT -> Int;
    bridgeStellarSeqNum,
    \* @type: Set(STELLAR_TX);
    bridgeStellarExecuted,
    \* @type: Set(HASH);
    refunded

INSTANCE StarbridgeEthToStellar

=============================================================================

