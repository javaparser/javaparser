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

package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.model.usages.typesystem.PrimitiveType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;
import me.tomassetti.symbolsolver.resolution.SymbolSolver;

import java.util.List;
import java.util.Optional;

public class FieldAccessContext extends AbstractJavaParserContext<FieldAccessExpr> {

    private static final String ARRAY_LENGTH_FIELD_NAME = "length";

    public FieldAccessContext(FieldAccessExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (wrappedNode.getFieldExpr().toString().equals(name)) {
            if (wrappedNode.getScope() instanceof ThisExpr) {
                Type typeOfThis = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
                return new SymbolSolver(typeSolver).solveSymbolInType(typeOfThis.asReferenceType().getTypeDeclaration(), name);
            }
        }
        return JavaParserFactory.getContext(wrappedNode.getParentNode(), typeSolver).solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode(), typeSolver).solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode(), typeSolver).solveMethod(name, argumentsTypes, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        Expression scope = wrappedNode.getScope();
        if (wrappedNode.getFieldExpr().toString().equals(name)) {
            Type typeOfScope = JavaParserFacade.get(typeSolver).getType(scope);
            if (typeOfScope.isArray() && name.equals(ARRAY_LENGTH_FIELD_NAME)) {
                return Optional.of(new Value(PrimitiveType.INT, ARRAY_LENGTH_FIELD_NAME, false));
            }
            if (typeOfScope.isReferenceType()) {
                Optional<Type> typeUsage = typeOfScope.asReferenceType().getFieldType(name);
                if (typeUsage.isPresent()) {
                    return Optional.of(new Value(typeUsage.get(), name, true));
                } else {
                    return Optional.empty();
                }
            } else {
                return Optional.empty();
            }
        } else {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
    }
}
