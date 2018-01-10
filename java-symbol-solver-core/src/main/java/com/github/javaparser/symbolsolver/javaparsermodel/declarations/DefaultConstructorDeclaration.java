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

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.Collections;
import java.util.List;

/**
 * This represents the default constructor added by the compiler for objects not declaring one.
 * It takes no parameters. See JLS 8.8.9 for details.
 *
 * @author Federico Tomassetti
 */
class DefaultConstructorDeclaration implements ResolvedConstructorDeclaration {

    private ResolvedClassDeclaration classDeclaration;

    DefaultConstructorDeclaration(ResolvedClassDeclaration classDeclaration) {
        this.classDeclaration = classDeclaration;
    }

    @Override
    public ResolvedClassDeclaration declaringType() {
        return classDeclaration;
    }

    @Override
    public int getNumberOfParams() {
        return 0;
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        throw new UnsupportedOperationException("The default constructor has not parameters");
    }

    @Override
    public String getName() {
        return classDeclaration.getName();
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return AccessSpecifier.PUBLIC;
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    @Override
    public int getNumberOfSpecifiedExceptions() {
        return 0;
    }

    @Override
    public ResolvedType getSpecifiedException(int index) {
        throw new UnsupportedOperationException("The default constructor does not throw exceptions");
    }
}
