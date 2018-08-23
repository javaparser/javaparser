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

package com.github.javaparser.symbolsolver.javaparsermodel.declarators;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class ParameterSymbolDeclarator extends AbstractSymbolDeclarator<Parameter> {

    public ParameterSymbolDeclarator(Parameter wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<ResolvedValueDeclaration> getSymbolDeclarations() {
        List<ResolvedValueDeclaration> symbols = new LinkedList<>();
        symbols.add(JavaParserSymbolDeclaration.parameter(wrappedNode, typeSolver));
        return symbols;
    }
}
