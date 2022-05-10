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
const_1652151904207720000 == 
{s1, s2}
----

\* MV CONSTANT definitions EthAddr
const_1652151904207721000 == 
{e1, e2, e3}
----

\* MV CONSTANT definitions Validator
const_1652151904207722000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions User
const_1652151904207723000 == 
{u1, u2}
----

\* SYMMETRY definition
symm_1652151904207724000 == 
Permutations(const_1652151904207722000)
----

\* CONSTANT definitions @modelParameterConstants:3BridgeStellarAddr
const_1652151904207725000 == 
CHOOSE addr \in StellarAddr : TRUE
----

\* CONSTANT definitions @modelParameterConstants:4BridgeEthAddr
const_1652151904207726000 == 
CHOOSE addr \in EthAddr : TRUE
----

\* CONSTANT definitions @modelParameterConstants:5MaxAmount
const_1652151904207727000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6StellarTxId
const_1652151904207728000 == 
EthTxId
----

\* CONSTANT definitions @modelParameterConstants:7EthTxId
const_1652151904207729000 == 
0..2
----

\* CONSTANT definitions @modelParameterConstants:8Threshold
const_1652151904207730000 == 
2
----

=============================================================================
\* Modification History
\* Created Mon May 09 20:05:04 PDT 2022 by nano
