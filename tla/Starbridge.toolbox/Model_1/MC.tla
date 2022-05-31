---- MODULE MC ----
EXTENDS Starbridge, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
e1, e2, e3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
u1, u2
----

\* MV CONSTANT definitions StellarAddr
const_1652153182353746000 == 
{s1, s2}
----

\* MV CONSTANT definitions EthAddr
const_1652153182353747000 == 
{e1, e2, e3}
----

\* MV CONSTANT definitions Validator
const_1652153182353748000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions User
const_1652153182353749000 == 
{u1, u2}
----

\* SYMMETRY definition
symm_1652153182353750000 == 
Permutations(const_1652153182353748000)
----

\* CONSTANT definitions @modelParameterConstants:3BridgeStellarAddr
const_1652153182353751000 == 
CHOOSE addr \in StellarAddr : TRUE
----

\* CONSTANT definitions @modelParameterConstants:4BridgeEthAddr
const_1652153182353752000 == 
CHOOSE addr \in EthAddr : TRUE
----

\* CONSTANT definitions @modelParameterConstants:5MaxAmount
const_1652153182353753000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6StellarTxId
const_1652153182353754000 == 
EthTxId
----

\* CONSTANT definitions @modelParameterConstants:7EthTxId
const_1652153182353755000 == 
0..2
----

\* CONSTANT definitions @modelParameterConstants:8Threshold
const_1652153182353756000 == 
2
----

=============================================================================
\* Modification History
\* Created Mon May 09 20:26:22 PDT 2022 by nano
