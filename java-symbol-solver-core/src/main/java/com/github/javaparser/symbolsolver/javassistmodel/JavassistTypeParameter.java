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

import javassist.bytecode.SignatureAttribute;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;

public class JavassistTypeParameter implements TypeParameterDeclaration {

    private SignatureAttribute.TypeParameter wrapped;
    private boolean declaredOnClass;
    private TypeSolver typeSolver;
    private String qualifier;

    public JavassistTypeParameter(SignatureAttribute.TypeParameter wrapped, boolean declaredOnClass, String qualifier, TypeSolver typeSolver) {
        this.wrapped = wrapped;
        this.declaredOnClass = declaredOnClass;
        this.typeSolver = typeSolver;
        this.qualifier = qualifier;
    }

    @Override
    public String toString() {
        return "JavassistTypeParameter{" +
                wrapped.getName()
                + '}';
    }

    @Override
    public String getName() {
        return wrapped.getName();
    }

    @Override
    public boolean declaredOnClass() {
        return declaredOnClass;
    }

    @Override
    public boolean declaredOnMethod() {
        return !declaredOnClass();
    }

    @Override
    public String getQualifiedName() {
        return String.format("%s.%s", qualifier, getName());
    }

    @Override
    public List<TypeParameterDeclaration.Bound> getBounds(TypeSolver typeSolver) {
        List<Bound> bounds = new ArrayList<>();
        if (wrapped.getClassBound() != null) {
            throw new UnsupportedOperationException(wrapped.getClassBound().toString());
        }
        for (SignatureAttribute.ObjectType ot : wrapped.getInterfaceBound()) {
            throw new UnsupportedOperationException(ot.toString());
        }
        return bounds;
    }
}
