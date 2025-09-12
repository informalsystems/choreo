This is a script for running choreo examples with `quint`.

This script requires [`txm`](https://www.npmjs.com/package/txm) to be
installed:

```sh
npm install -g txm
```

*NOTE*: these tests only check that particular invocations succeed or fail.
Tests marked as "should succeed" are expected to pass with the given invariants.
Tests marked as "should fail" are expected to find counterexamples to the invariants.

All tests in the following cases are run as commands to `bash`.

<!-- !test program
bash -
-->

## Tendermint Examples

### OK on tendermint valid module - run with invariants

<!-- !test check tendermint valid - run with invariants -->
    cd examples/tendermint && quint run tendermint.qnt --main valid --invariant="agreement and validity and accountability" --max-samples=20 --verbosity 1

### OK on tendermint valid module - test

<!-- !test check tendermint valid - test -->
    cd examples/tendermint && quint test tendermint.qnt --main valid --max-samples=20 --verbosity 1

### FAIL on tendermint no_agreement module - run with agreement (should find counterexample)

<!-- !test exit 1 -->
<!-- !test check tendermint no_agreement - run with agreement (should fail) -->
    cd examples/tendermint && quint run tendermint.qnt --main no_agreement --invariant=agreement --verbosity 1

### OK on tendermint no_agreement module - run with accountability only

<!-- !test check tendermint no_agreement - run with accountability -->
    cd examples/tendermint && quint run tendermint.qnt --main no_agreement --invariant=accountability --max-samples=20 --verbosity 1

### OK on tendermint no_agreement module - test

<!-- !test check tendermint no_agreement - test -->
    cd examples/tendermint && quint test tendermint.qnt --main no_agreement --max-samples=20 --verbosity 1

## Alpenglow Examples

### FAIL on alpenglow some_byz module - run with fastFinalizedWitness

<!-- !test exit 1 -->
<!-- !test check alpenglow some_byz - run with fastFinalizedWitness -->
    cd examples/alpenglow && quint run alpenglow.qnt --main some_byz --invariant fastFinalizedWitness --verbosity 1

### FAIL on alpenglow too_many_byz_1 module - run with agreement (should find counterexample)

<!-- !test exit 1 -->
<!-- !test check alpenglow too_many_byz_1 - run with agreement (should fail) -->
    cd examples/alpenglow && quint run alpenglow.qnt --main too_many_byz_1 --invariant agreement --verbosity 1

### FAIL on alpenglow too_many_byz module - run with agreement (should find counterexample)

<!-- !test exit 1 -->
<!-- !test check alpenglow too_many_byz - run with agreement (should fail) -->
    cd examples/alpenglow && quint run alpenglow.qnt --main too_many_byz --invariant agreement --verbosity 1

## MonadBFT Examples

### OK on monadbft instance - run with missing_tip_w

<!-- !test check monadbft instance - run with missing_tip_w -->
    cd examples/monadbft && quint run instance.qnt --max-steps 50 --invariant missing_tip_w --hide monadbft::choreo::s --max-samples=20 --verbosity 1

## Additional Verification Tests

### OK on typecheck choreo

<!-- !test check choreo - typecheck -->
    quint typecheck choreo.qnt

### OK on run template

<!-- !test check template - typecheck -->
    quint run template.qnt
