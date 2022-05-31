# Starbridge

This repository contains formal models related to the Starbridge project.

Notably,
[starbridge.ivy](https://github.com/nano-o/Starbridge/blob/main/ivy/shared/starbridge.ivy)
contains a model of the Ethereum to Stellar deposit flow (with refunds) and
a safety proof in the form of an inductive invariant. Check it with `ivy_check
complete=fo starbridge.ivy`.
