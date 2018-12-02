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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.LambdaExprContext;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;

import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class JavaParserParameterDeclaration implements ResolvedParameterDeclaration {

    private Parameter wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserParameterDeclaration(Parameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return true;
    }

    @Override
    public boolean isVariadic() {
        return wrappedNode.isVarArgs();
    }

    @Override
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ResolvedType getType() {
        if (wrappedNode.getType() instanceof UnknownType && JavaParserFactory.getContext(wrappedNode, typeSolver) instanceof LambdaExprContext) {
            Optional<Value> value = JavaParserFactory.getContext(wrappedNode, typeSolver).solveSymbolAsValue(wrappedNode.getNameAsString());
            if (value.isPresent()) {
                return value.get().getType();
            }
        }
        ResolvedType res = JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), wrappedNode);
        if (isVariadic()) {
            res = new ResolvedArrayType(res);
        }
        return res;
    }

    @Override
    public ResolvedParameterDeclaration asParameter() {
        return this;
    }

    /**
     * Returns the JavaParser node associated with this JavaParserParameterDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public Parameter getWrappedNode() {
        return wrappedNode;
    }


}
