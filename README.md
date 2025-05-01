# Formal_Diamond_iO


Formal Verification of Lattice-Based Indistinguishability Obfuscation

## Overview

FormalDiamond aims to formally verify the innovative obfuscation construction proposed in the paper "Diamond iO: A Straightforward Construction of Indistinguishability Obfuscation from Lattices" by Suegami & Bottazzi (February 2025). This paper introduces a diamond-shaped key-switching operation that eliminates the dependency on bootstrapping techniques from Functional Encryption (FE) to Indistinguishability Obfuscation (iO), which has been a significant barrier in existing iO constructions.

Using Lean 4's powerful type system and proof assistant capabilities, this project aims to formally verify the following components:

- Learning With Errors (LWE) assumption
- Evasive LWE assumption
- The newly proposed all-product LWE assumption
- Correctness of the Diamond iO construction
- Security (indistinguishability) of the Diamond iO construction

## Prerequisites

- Lean 4 (latest nightly build recommended)
- elan (Lean version manager)
- mathlib4

## Setup

After cloning this repository, run the following commands to set up the project:

```bash
# Update dependencies
lake update

# Download pre-built mathlib files (important step!)
lake exe cache get

# Build the project
lake build
```

## Project Structure
```txt
.
├── FormalDiamond/             # Library source files
│   ├── LWE.lean               # Definition of LWE assumption
│   ├── EvasiveLWE.lean        # Definition of evasive LWE assumption
│   ├── AllProductLWE.lean     # Definition of all-product LWE assumption
│   ├── BGGPlus.lean           # Implementation of BGG+ encoding
│   └── DiamondIO.lean         # Implementation of Diamond iO construction
├── FormalDiamond.lean         # Library root file
├── Main.lean                  # Main file
└── lakefile.lean              # Lake package configuration
```
