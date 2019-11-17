/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.List;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

/**
 * @author Federico Tomassetti
 */
public class ObjectCreationContext extends AbstractJavaParserContext<ObjectCreationExpr> {

    public ObjectCreationContext(ObjectCreationExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if (wrappedNode.getScope().isPresent()) {
            Expression scope = wrappedNode.getScope().get();
            ResolvedType scopeType = JavaParserFacade.get(typeSolver).getType(scope);
            if (scopeType.isReferenceType()) {
                ResolvedReferenceType referenceType = scopeType.asReferenceType();
                for (ResolvedTypeDeclaration it : referenceType.getTypeDeclaration().internalTypes()) {
                    if (it.getName().equals(name)) {
                        return SymbolReference.solved(it);
                    }
                }
            }
            throw new UnsolvedSymbolException("Unable to solve qualified object creation expression in the context of expression of type " + scopeType.describe());
        }
        // find first parent node that is not an object creation expression to avoid stack overflow errors, see #1711
        Node parentNode = requireParentNode(wrappedNode);
        while (parentNode instanceof ObjectCreationExpr) {
            parentNode = requireParentNode(parentNode);
        }
        return JavaParserFactory.getContext(parentNode, typeSolver).solveType(name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        return JavaParserFactory.getContext(requireParentNode(wrappedNode), typeSolver).solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return JavaParserFactory.getContext(requireParentNode(wrappedNode), typeSolver).solveMethod(name, argumentsTypes, false);
    }

}
