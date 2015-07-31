package me.tomassetti.symbolsolver.model;

import com.github.javaparser.ast.type.Type;

/**
 * Created by federico on 28/07/15.
 */
public interface SymbolDeclaration {
    String getName();
    boolean isField();
    boolean isParameter();

    boolean isType();

    TypeDeclaration asTypeDeclaration();

    TypeDeclaration getType();
}
