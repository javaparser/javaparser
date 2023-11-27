/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.resolution.Navigator.demandParentNode;

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
                if(typeOfThis.asReferenceType().getTypeDeclaration().isPresent()) {
                    return new SymbolSolver(typeSolver).solveSymbolInType(
                            typeOfThis.asReferenceType().getTypeDeclaration().get(),
                            name
                    );
                }
            }
        }
        return JavaParserFactory.getContext(demandParentNode(wrappedNode), typeSolver).solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {
        return JavaParserFactory.getContext(demandParentNode(wrappedNode), typeSolver).solveType(name, typeArguments);
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
                return solveSymbolAsValue(name, typeOfScope.asReferenceType());
            }
                    if (typeOfScope.isConstraint()) {
                return solveSymbolAsValue(name, typeOfScope.asConstraintType().getBound().asReferenceType());
            }
            return Optional.empty();
        }
        return solveSymbolAsValueInParentContext(name);
    }

    /*
     * Try to resolve the name parameter as a field of the reference type
     */
    private Optional<Value> solveSymbolAsValue(String name, ResolvedReferenceType type) {
        Optional<ResolvedReferenceTypeDeclaration> optionalTypeDeclaration = type.getTypeDeclaration();
        if (optionalTypeDeclaration.isPresent()) {
            ResolvedReferenceTypeDeclaration typeDeclaration = optionalTypeDeclaration.get();
            if (typeDeclaration.isEnum()) {
                ResolvedEnumDeclaration enumDeclaration = (ResolvedEnumDeclaration) typeDeclaration;
                if (enumDeclaration.hasEnumConstant(name)) {
                    return Optional.of(new Value(enumDeclaration.getEnumConstant(name).getType(), name));
                }
            }
        }
        Optional<ResolvedType> typeUsage = type.getFieldType(name);
        return typeUsage.map(resolvedType -> new Value(resolvedType, name));
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
        return SymbolReference.unsolved();
    }
}
