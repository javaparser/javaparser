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

package com.github.javaparser.symbolsolver.model.resolution;

import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.usages.typesystem.Type;

/**
 * @author Federico Tomassetti
 */
public class Value {
    private Type type;
    private String name;
    private boolean field;

    public Value(Type type, String name, boolean field) {
        this.type = type;
        this.name = name;
        this.field = field;
    }

    public static Value from(ValueDeclaration decl, TypeSolver typeSolver) {
        Type type = decl.getType();
        return new Value(type, decl.getName(), decl.isField());
    }

    @Override
    public String toString() {
        return "Value{" +
                "typeUsage=" + type +
                ", name='" + name + '\'' +
                ", field=" + field +
                '}';
    }

    public String getName() {
        return name;
    }

    public Type getUsage() {
        return type;
    }

}
