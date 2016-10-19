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

package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.List;

public class ClassOrInterfaceDeclarationContext implements Context {

    private Class<?> wrapped;

    public ClassOrInterfaceDeclarationContext(Class<?> clazz) {
        this.wrapped = clazz;
    }


    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Field field : wrapped.getFields()) {
            if (Modifier.isStatic(field.getModifiers()) && field.getName().equals(name)) {
                if (field.getDeclaringClass().getCanonicalName().equals(wrapped.getCanonicalName())
                        || !Modifier.isPrivate(field.getModifiers())) {
                    return SymbolReference.solved(new ReflectionFieldDeclaration(field, typeSolver));
                }
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getParent() {
        throw new UnsupportedOperationException();
    }

}
