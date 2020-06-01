# Create generators based on the metamodel

## Status

Accepted (quite a few years ago).

## Context

[The metamodel has information about which nodes exist, and what their properties are.](create_metamodel.md) The quality of the source code for the AST nodes and the visitors is currently low, with many inconsistencies that could have been avoided with generating this code. 

## Decision

Create a tool that updates the AST nodes and visitors as much as possible with the information from the metamodel.

Create a module with reusable code so that users can build their own generators.

## Consequences

The code quality from the nodes and visitors will increase dramatically,
and maintenance will be simplified. 
