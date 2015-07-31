package me.tomassetti.symbolsolver.model;

import java.util.List;

/**
 * Created by federico on 31/07/15.
 */
public interface TypeDeclaration extends SymbolDeclaration {
    String getQualifiedName();
    Context getContext();

    SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes);
}
