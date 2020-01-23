/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver.javaparsermodel.contexts;

import org.javaparser.ast.Node;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.expr.ObjectCreationExpr;
import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.resolution.types.ResolvedReferenceType;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.List;

import static org.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

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
        Node parentNode = demandParentNode(wrappedNode);
        while (parentNode instanceof ObjectCreationExpr) {
            parentNode = demandParentNode(parentNode);
        }
        return JavaParserFactory.getContext(parentNode, typeSolver).solveType(name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        return JavaParserFactory.getContext(demandParentNode(wrappedNode), typeSolver).solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return JavaParserFactory.getContext(demandParentNode(wrappedNode), typeSolver).solveMethod(name, argumentsTypes, false);
    }

}
