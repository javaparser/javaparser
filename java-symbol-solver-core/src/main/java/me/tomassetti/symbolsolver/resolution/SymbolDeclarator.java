package me.tomassetti.symbolsolver.resolution;

import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;

import java.util.List;

public interface SymbolDeclarator {

    List<ValueDeclaration> getSymbolDeclarations();

}
