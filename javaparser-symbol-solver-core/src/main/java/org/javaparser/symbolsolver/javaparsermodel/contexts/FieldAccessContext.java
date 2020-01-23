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

import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.expr.FieldAccessExpr;
import org.javaparser.ast.expr.ThisExpr;
import org.javaparser.resolution.declarations.*;
import org.javaparser.resolution.types.ResolvedPrimitiveType;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.model.resolution.Value;
import org.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import static org.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class FieldAccessContext extends AbstractJavaParserContext<FieldAccessExpr> {

    private static final String ARRAY_LENGTH_FIELD_NAME = "length";

    public FieldAccessContext(FieldAccessExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        if (wrappedNode.getName().toString().equals(name)) {
            if (wrappedNode.getScope() instanceof ThisExpr) {
                ResolvedType typeOfThis = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
                return new SymbolSolver(typeSolver).solveSymbolInType(typeOfThis.asReferenceType().getTypeDeclaration(), name);
            }
        }
        return JavaParserFactory.getContext(demandParentNode(wrappedNode), typeSolver).solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return JavaParserFactory.getContext(demandParentNode(wrappedNode), typeSolver).solveType(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> parameterTypes, boolean staticOnly) {
        return JavaParserFactory.getContext(demandParentNode(wrappedNode), typeSolver).solveMethod(name, parameterTypes, false);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        Expression scope = wrappedNode.getScope();
        if (wrappedNode.getName().toString().equals(name)) {
            ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getType(scope);
            if (typeOfScope.isArray() && name.equals(ARRAY_LENGTH_FIELD_NAME)) {
                return Optional.of(new Value(ResolvedPrimitiveType.INT, ARRAY_LENGTH_FIELD_NAME));
            }
            if (typeOfScope.isReferenceType()) {
                if (typeOfScope.asReferenceType().getTypeDeclaration().isEnum()) {
                    ResolvedEnumDeclaration enumDeclaration = (ResolvedEnumDeclaration)typeOfScope.asReferenceType().getTypeDeclaration();
                    if (enumDeclaration.hasEnumConstant(name)) {
                        return Optional.of(new Value(enumDeclaration.getEnumConstant(name).getType(), name));
                    }
                }
                Optional<ResolvedType> typeUsage = typeOfScope.asReferenceType().getFieldType(name);
                return typeUsage.map(resolvedType -> new Value(resolvedType, name));
            } else {
                return Optional.empty();
            }
        } else {
            return getParent().solveSymbolAsValue(name);
        }
    }

    public SymbolReference<ResolvedValueDeclaration> solveField(String name) {
        Collection<ResolvedReferenceTypeDeclaration> rrtds = findTypeDeclarations(Optional.of(wrappedNode.getScope()));
        for (ResolvedReferenceTypeDeclaration rrtd : rrtds) {
            if (rrtd.isEnum()) {
                Optional<ResolvedEnumConstantDeclaration> enumConstant = rrtd.asEnum().getEnumConstants().stream().filter(c -> c.getName().equals(name)).findFirst();
                if (enumConstant.isPresent()) {
                    return SymbolReference.solved(enumConstant.get());
                }
            }
            try {
                return SymbolReference.solved(rrtd.getField(wrappedNode.getName().getId()));
            } catch (Throwable t) {
            }
        }
        return SymbolReference.unsolved(ResolvedFieldDeclaration.class);
    }
}
