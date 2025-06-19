# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 project for formal verification of lattice-based indistinguishability obfuscation, specifically implementing and verifying the Diamond iO construction from the paper by Suegami & Bottazzi. The project focuses on formally proving cryptographic assumptions and constructions using Lean's type system.

## Essential Commands

### Building and Development
```bash
# Update dependencies
lake update

# Download pre-built mathlib files (crucial for performance)
lake exe cache get

# Build the entire project
lake build

# Build specific target
lake build FormalDiamondIO

# Check syntax without building
lean --check FormalDiamondIO.lean
```

### Lean Version Management
- Project uses Lean 4 v4.19.0 (specified in lean-toolchain)
- Use `elan` to manage Lean versions if needed

## Architecture

### Core Components
- **LWE Module** (`FormalDiamondIO/LWE.lean`): Defines Learning With Errors parameters, variants (Search/Decision), and discrete Gaussian distributions
- **Basic Module** (`FormalDiamondIO/Basic.lean`): Currently minimal, likely foundation for shared definitions
- **Root Module** (`FormalDiamondIO.lean`): Library entry point that imports core modules

### Key Structures
- `LWEParams`: Encapsulates LWE problem parameters (dimension n, sample size m, modulus q, Gaussian parameter α)
- `LWEVariant`: Distinguishes between Search and Decision variants of LWE
- `DiscreteGaussian`: Type for discrete Gaussian distributions over ZMod q
- `SampleGaussian`: Sampling function type for Gaussian distributions

### Project Configuration
- Uses mathlib4 as primary dependency
- Default build target: `FormalDiamondIO`
- Lean options: Unicode function notation enabled, auto-implicit disabled

## Development Notes

### Working with Mathlib
- Always run `lake exe cache get` after `lake update` to download precompiled mathlib files
- The project depends heavily on mathlib's algebraic and cryptographic foundations

### Cryptographic Context
The codebase implements formal verification of:
- LWE assumption variants
- Evasive LWE assumption (planned)
- All-product LWE assumption (planned)
- Diamond iO construction correctness and security (planned)

### File Organization
Most development should occur in the `FormalDiamondIO/` directory. The root `FormalDiamondIO.lean` file serves as the library interface and should import new modules added to the library.