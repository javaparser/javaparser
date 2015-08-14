package me.tomassetti.symbolsolver.model.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.FieldDeclaration;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 31/07/15.
 */
public interface TypeDeclaration extends Declaration, TypeParametrized {
    String getQualifiedName();
    Context getContext();

    SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver);

    /**
     * Get how the type is used in the given context.
     * @param node
     * @return
     */
    TypeUsage getUsage(Node node);

    boolean isAssignableBy(TypeUsage typeUsage);

    boolean isTypeVariable();

    FieldDeclaration getField(String name);

    boolean hasField(String name);


    default Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
}
