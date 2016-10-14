package me.tomassetti.symbolsolver.core.resolution;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.util.List;
import java.util.Optional;

/**
 * Context is very similar to scope.
 * In the context we look for solving symbols.
 *
 * @author Federico Tomassetti
 */
public interface Context {

    Context getParent();

    /* Type resolution */

    default Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
        return Optional.empty();
    }

    default SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        Context parent = getParent();
        if (parent == null) {
            return SymbolReference.unsolved(TypeDeclaration.class);
        } else {
            return getParent().solveType(name, typeSolver);
        }
    }

    /* Symbol resolution */

    SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver);

    default Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        SymbolReference<? extends ValueDeclaration> ref = solveSymbol(name, typeSolver);
        if (ref.isSolved()) {
            Value value = Value.from(ref.getCorrespondingDeclaration(), typeSolver);
            return Optional.of(value);
        } else {
            return Optional.empty();
        }
    }

    /* Methods resolution */

    /**
     * We find the method declaration which is the best match for the given name and list of typeParametersValues.
     */
    SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver);

    /**
     * Similar to solveMethod but we return a MethodUsage. A MethodUsage corresponds to a MethodDeclaration plus the
     * resolved type variables.
     */
    default Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        SymbolReference<MethodDeclaration> methodSolved = solveMethod(name, parameterTypes, typeSolver);
        if (methodSolved.isSolved()) {
            MethodDeclaration methodDeclaration = methodSolved.getCorrespondingDeclaration();
            MethodUsage methodUsage = ContextHelper.resolveTypeVariables(this, methodDeclaration, parameterTypes);//methodDeclaration.resolveTypeVariables(this, parameterTypes);
            return Optional.of(methodUsage);
        } else {
            return Optional.empty();
        }
    }
}
