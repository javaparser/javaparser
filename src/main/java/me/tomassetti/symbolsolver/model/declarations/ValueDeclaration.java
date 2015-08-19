package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

/**
 * @author Federico Tomassetti
 */
public interface ValueDeclaration extends Declaration {

    TypeDeclaration getType(TypeSolver typeSolver);

    default TypeUsage getTypeUsage(TypeSolver typeSolver) {
        return new TypeUsageOfTypeDeclaration(getType(typeSolver));
    }
}
