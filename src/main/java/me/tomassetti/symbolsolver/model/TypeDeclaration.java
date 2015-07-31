package me.tomassetti.symbolsolver.model;

/**
 * Created by federico on 31/07/15.
 */
public interface TypeDeclaration extends SymbolDeclaration {
    String getQualifiedName();
    Context getContext();
}
