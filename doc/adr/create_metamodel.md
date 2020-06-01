# Create a metamodel

## Status

Accepted (quite a few years ago).

## Context

The AST nodes and the visitors used to be very inconsistently implemented.
Much of this code is repetitive, and can be automatically generated.

## Decision

Create a model that contains all useful information about the nodes in the AST.

## Consequences

This can be used as a to generate code that deals with nodes, and has a lot of repetition.
Specifically: the AST node source code, and the visitors.

