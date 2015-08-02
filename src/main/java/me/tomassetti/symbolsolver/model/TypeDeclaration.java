package me.tomassetti.symbolsolver.model;

import com.github.javaparser.ast.Node;

import java.util.List;

/**
 * Created by federico on 31/07/15.
 */
public interface TypeDeclaration extends SymbolDeclaration {
    String getQualifiedName();
    Context getContext();

    SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes);

    /**
     * Get how the type is used in the given context.
     * @param node
     * @return
     */
    TypeUsage getUsage(Node node);

    boolean isAssignableBy(TypeUsage typeUsage);
}
