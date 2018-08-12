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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class VariableDeclaratorContext extends AbstractJavaParserContext<VariableDeclarator> {

    public VariableDeclaratorContext(VariableDeclarator wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        if (wrappedNode.getInitializer().isPresent() && wrappedNode.getInitializer().get() == child) {
            return Collections.singletonList(wrappedNode);
        }
        return Collections.emptyList();
    }

}
