package com.github.javaparser.resolution;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.List;
import java.util.Optional;

public interface Solver {

    SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, Context context);

    SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, Node node);

    Optional<Value> solveSymbolAsValue(String name, Context context);

    Optional<Value> solveSymbolAsValue(String name, Node node);

    SymbolReference<? extends ResolvedTypeDeclaration> solveType(String name, Context context);

    SymbolReference<? extends ResolvedTypeDeclaration> solveType(String name, Node node);

    MethodUsage solveMethod(String methodName, List<ResolvedType> argumentsTypes, Context context);

    MethodUsage solveMethod(String methodName, List<ResolvedType> argumentsTypes, Node node);

    ResolvedTypeDeclaration solveType(Type type);

    ResolvedType solveTypeUsage(String name, Context context);

    /**
     * Solve any possible visible symbols including: fields, internal types, type variables, the type itself or its
     * containers.
     * <p>
     * It should contain its own private fields but not inherited private fields.
     */
    SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInType(ResolvedTypeDeclaration typeDeclaration,
                                                                          String name);

    /**
     * Try to solve a symbol just in the declaration, it does not delegate to the container.
     *
     * @deprecated Similarly to solveType this should eventually disappear as the symbol resolution logic should be more general
     * and do not be specific to JavaParser classes like in this case.
     */
    SymbolReference<ResolvedTypeDeclaration> solveTypeInType(ResolvedTypeDeclaration typeDeclaration, String name);

    /**
     * Convert a {@link Class} into the corresponding {@link ResolvedType}.
     *
     * @param clazz The class to be converted.
     * @return The class resolved.
     */
    ResolvedType classToResolvedType(Class<?> clazz);

}