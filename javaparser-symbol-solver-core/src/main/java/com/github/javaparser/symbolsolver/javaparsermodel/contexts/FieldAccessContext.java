/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;
import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

/**
 * @author Federico Tomassetti
 */
public class FieldAccessContext extends AbstractJavaParserContext<FieldAccessExpr> {

    private static final String ARRAY_LENGTH_FIELD_NAME = "length";

    public FieldAccessContext(FieldAccessExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (wrappedNode.getName().toString().equals(name)) {
            if (wrappedNode.getScope() instanceof ThisExpr) {
                ResolvedType typeOfThis = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
                return new SymbolSolver(typeSolver).solveSymbolInType(typeOfThis.asReferenceType().getTypeDeclaration(), name);
            }
        }
        return JavaParserFactory.getContext(requireParentNode(wrappedNode), typeSolver).solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(requireParentNode(wrappedNode), typeSolver).solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> parameterTypes, boolean staticOnly, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(requireParentNode(wrappedNode), typeSolver).solveMethod(name, parameterTypes, false, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        Expression scope = wrappedNode.getScope();
        if (wrappedNode.getName().toString().equals(name)) {
            ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getType(scope);
            if (typeOfScope.isArray() && name.equals(ARRAY_LENGTH_FIELD_NAME)) {
                return Optional.of(new Value(ResolvedPrimitiveType.INT, ARRAY_LENGTH_FIELD_NAME));
            }
            if (typeOfScope.isReferenceType()) {
                Optional<ResolvedType> typeUsage = typeOfScope.asReferenceType().getFieldType(name);
                return typeUsage.map(resolvedType -> new Value(resolvedType, name));
            } else {
                return Optional.empty();
            }
        } else {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
    }

    public SymbolReference<ResolvedFieldDeclaration> solveField(String name, TypeSolver typeSolver) {
        Collection<ResolvedReferenceTypeDeclaration> rrtds = findTypeDeclarations(Optional.of(wrappedNode.getScope()), typeSolver);
        for (ResolvedReferenceTypeDeclaration rrtd : rrtds) {
            try {
                return SymbolReference.solved(rrtd.getField(wrappedNode.getName().getId()));
            } catch (Throwable t) {
            }
        }
        return SymbolReference.unsolved(ResolvedFieldDeclaration.class);
    }
}
