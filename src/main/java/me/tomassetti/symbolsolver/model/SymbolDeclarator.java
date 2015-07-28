package me.tomassetti.symbolsolver.model;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public interface SymbolDeclarator {

    public List<SymbolDeclaration> getSymbolDeclarations();
    public List<MethodDeclaration> getMethodDeclarations();
}
