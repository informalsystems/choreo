# Tendermint Consensus specification in Quint

A Quint specification of MonadBFT consensus, based on the
[paper](https://arxiv.org/abs/2502.20692), using the Consensus State Machine Interface (CSMI) library.

## Findings
The specification is a trasnlation of the pseudo-code in the paper. The main goal of this work is to check some properties of the protocol.
The file `monadbft.qnt` contains warning annotations under `// Warning` that indicate unspecified behavior in the paper or potential issues in the protocol.

## Model

The model is reactive to messages. Transitions in the state machine are either a message being received or a timeout expiring. 
Also, all reactions to a single message are done in one atomic step.
We also keep track of evidence to investigate protocol behavior. This is kept in a `bookkeeping` field, which is not used by the protocol itself, only to check properties.

## Properties

We define the following properties:
- **safety**
- **no-tail-forking** (NTF)

To check that they hold in the absence of byzantine nodes, run the simulator:

``` sh
$ quint run monadbft.qnt --main test --max-steps=200 --invariant=safety
```

``` sh
$ quint run monadbft.qnt --main test --max-steps=200 --invariant=ntf
```
to disable timeout events in the simulator, run with the option `--step=step_no_timeout`

## Witnesses

We provide witnesses to show interesting execution scenarios. To look for a case where a block is reproposed in a subsequent view, run:

``` sh
$ quint run monadbft.qnt --main test --max-steps=200 --invariant=reproposal
```
