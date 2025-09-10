# Testing Guide for Choreo Examples

This document describes how to run tests for all choreo protocol examples.

## Overview

The test suite validates that:
1. **Positive tests**: Valid protocols satisfy their safety properties
2. **Negative tests**: Invalid configurations properly fail and find counterexamples
3. **Syntax tests**: All examples parse and typecheck correctly

## Test Configuration

Tests use a low sample count (`--max-samples=20`) for fast feedback, except for negative tests which run without limits to ensure they find counterexamples.

## Prerequisites

- [Quint](https://github.com/informalsystems/quint) must be installed and available in PATH
- For npm/txm approach: Node.js and npm

## Running Tests

### Option 1: Using txm (Recommended)

[`txm`](https://www.npmjs.com/package/txm) is a test runner that executes commands embedded in markdown files.

1. Install txm:
   ```bash
   npm install -g txm
   ```

2. Run tests:
   ```bash
   txm examples-tests.md
   ```

3. For verbose output:
   ```bash
   txm examples-tests.md --verbose
   ```

### Option 2: Using npm scripts

1. Install dependencies:
   ```bash
   npm install
   ```

2. Run tests:
   ```bash
   npm test
   ```
## Adding New Tests

To add tests for new examples:

1. Add the commands as comments in your `.qnt` files:
   ```
   // quint run myprotocol.qnt --main valid --invariant=safety
   // quint test myprotocol.qnt --main valid
   ```

2. Add corresponding test cases to `examples-tests.md`:
   ```markdown
   ### OK on myprotocol valid - run with safety

   <!-- !test check myprotocol valid - run with safety -->
       cd examples/myprotocol && quint run myprotocol.qnt --main valid --invariant=safety --max-samples=20
   ```

4. For negative tests (expected failures), use:
   ```markdown
   ### FAIL on myprotocol invalid - run with safety (should find counterexample)

   <!-- !test exit 1 -->
   <!-- !test check myprotocol invalid - run with safety (should fail) -->
       cd examples/myprotocol && quint run myprotocol.qnt --main invalid --invariant=safety
   ```
