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

import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

/**
 * Any type of value.
 *
 * @author Federico Tomassetti
 */
public class Value {
    private ResolvedType type;
    private String name;

    public Value(ResolvedType type, String name) {
        this.type = type;
        this.name = name;
    }

    /**
     * Create a Value from a ValueDeclaration.
     */
    public static Value from(ResolvedValueDeclaration decl) {
        ResolvedType type = decl.getType();
        return new Value(type, decl.getName());
    }

    @Override
    public String toString() {
        return "Value{" +
                "typeUsage=" + type +
                ", name='" + name + '\'' +
                '}';
    }

    public String getName() {
        return name;
    }

    public ResolvedType getType() {
        return type;
    }

}
