package me.tomassetti.symbolsolver.model.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;

/**
 * Created by federico on 31/07/15.
 */
public interface TypeDeclaration extends Declaration, TypeParametrized {
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
