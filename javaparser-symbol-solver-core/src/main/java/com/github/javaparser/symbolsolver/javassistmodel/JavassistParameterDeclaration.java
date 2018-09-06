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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.CtClass;

/**
 * @author Federico Tomassetti
 */
public class JavassistParameterDeclaration implements ResolvedParameterDeclaration {
    private ResolvedType type;
    private TypeSolver typeSolver;
    private boolean variadic;
    private String name;

    public JavassistParameterDeclaration(CtClass type, TypeSolver typeSolver, boolean variadic, String name) {
        this(JavassistFactory.typeUsageFor(type, typeSolver), typeSolver, variadic, name);
    }

    public JavassistParameterDeclaration(ResolvedType type, TypeSolver typeSolver, boolean variadic, String name) {
        this.name = name;
        this.type = type;
        this.typeSolver = typeSolver;
        this.variadic = variadic;
    }

    @Override
    public String toString() {
        return "JavassistParameterDeclaration{" +
                "type=" + type +
                ", typeSolver=" + typeSolver +
                ", variadic=" + variadic +
                '}';
    }

    @Override
    public boolean hasName() {
        return name != null;
    }

    @Override
    public String getName() {
        return name;
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
        return variadic;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public ResolvedType getType() {
        return type;
    }
}
