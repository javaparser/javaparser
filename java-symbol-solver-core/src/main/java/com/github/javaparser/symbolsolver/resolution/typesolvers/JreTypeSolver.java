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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;

public class JreTypeSolver implements TypeSolver {

    private TypeSolver parent;

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        if (name.startsWith("java.") || name.startsWith("javax.")) {
            try {
                Class<?> clazz = JreTypeSolver.class.getClassLoader().loadClass(name);
                if (clazz.isInterface()) {
                    return SymbolReference.solved(new ReflectionInterfaceDeclaration(clazz, getRoot()));
                } else {
                    return SymbolReference.solved(new ReflectionClassDeclaration(clazz, getRoot()));
                }
            } catch (ClassNotFoundException e) {
                return SymbolReference.unsolved(TypeDeclaration.class);
            }
        } else {
            return SymbolReference.unsolved(TypeDeclaration.class);
        }
    }

}
