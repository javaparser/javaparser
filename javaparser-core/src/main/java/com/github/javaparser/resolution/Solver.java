/*
 * Copyright (C) 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
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
    SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInType(ResolvedTypeDeclaration typeDeclaration, String name);

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
     *
     * @return The class resolved.
     */
    ResolvedType classToResolvedType(Class<?> clazz);
}
