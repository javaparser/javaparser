package me.tomassetti.symbolsolver.resolution;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public interface SymbolDeclarator {

    public List<ValueDeclaration> getSymbolDeclarations();
    public List<MethodDeclaration> getMethodDeclarations();
}
