/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import java.util.List;

/**
 * Context of the types named in the extends and implements clauses of a type declaration.
 * <p>
 * The member types of the declaration are not in scope in these clauses (JLS 6.3): only its type parameters are,
 * then the context containing the declaration.
 */
public class TypeDeclarationExtendsContext extends AbstractJavaParserContext<TypeDeclaration<?>> {

    public TypeDeclarationExtendsContext(TypeDeclaration<?> wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {
        if (wrappedNode instanceof NodeWithTypeParameters) {
            for (TypeParameter typeParameter : ((NodeWithTypeParameters<?>) wrappedNode).getTypeParameters()) {
                if (typeParameter.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(typeParameter, typeSolver));
                }
            }
        }

        return super.solveType(name, typeArguments);
    }
}
