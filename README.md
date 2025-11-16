# Zippel Compiler

![Tests](https://github.com/elefthei/zippel/actions/workflows/rust.yml/badge.svg)

Zippel is a compiler that translates code written in the Zippel language for cryptographic protocols,
into optimized and safe prover and verifier code. This is a prototype and should not be used
for real systems.

## Table of Contents

- [Introduction](#introduction)
- [Features](#features)
- [Installation](#installation)
- [Usage](#usage)
- [Zippel Language Overview](#zippel-language-overview)
- [Examples](#examples)
- [Contributing](#contributing)
- [License](#license)

## Introduction

The Zippel compiler serves as a bridge between the Zippel language, a language designed for expressing cryptographic
protocols, and the zippel runtime designed to run protocols either as prover or verifier, with high-assurances
for the cryptographic properties of the protocol (soundness, completeness, zero-knowledge).

## Features

- **Compilation**: Translates Zippel language code into prover and verifier code.
- **Error Checking**: Provides detailed error messages for issues in the Zippel code.
- **Extensibility**: Easily extendable to support new constructs and cryptographic primitives.

## Installation

To install the Zippel compiler, you need to have [Rust](https://www.rust-lang.org/) installed on your system. Once Rust is set up, follow these steps:

1. Clone the repository:
   ```bash
   git clone https://github.com/elefthei/zippel
   cd zippel
   ```
2. Install Gurobi and licence at [Gurobi](https://www.gurobi.com/)
3. Build zippel:
   ```bash
   GUROBI_LIBNAME="gurobi110" cargo build
   ```

## Usage
To create an example, add a .zippel file to the examples folder with the zippel code. Then create a new folder in examples. You can copy from the ipa example, making sure to switch file path and arguments.
## Zippel Language Overview
## Examples
## Contributing
## License

MIT License

Copyright (c) 2024 University of Pennsylvania | Distributed Systems Lab

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
