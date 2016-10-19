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

package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.util.List;

/**
 * @author Federico Tomassetti
 */
public interface TypeParameterDeclaration {

    static TypeParameterDeclaration onClass(final String name, String classQName, List<Bound> bounds) {
        return new TypeParameterDeclaration() {
            @Override
            public String getName() {
                return name;
            }

            @Override
            public boolean declaredOnClass() {
                return true;
            }

            @Override
            public boolean declaredOnMethod() {
                return false;
            }

            @Override
            public String getQualifiedName() {
                return String.format("%s.%s", classQName, name);
            }

            @Override
            public List<Bound> getBounds(TypeSolver typeSolver) {
                return bounds;
            }

            @Override
            public String toString() {
                return "TypeParameter onClass " + name;
            }
        };
    }

    String getName();

    boolean declaredOnClass();

    boolean declaredOnMethod();

    String getQualifiedName();

    List<Bound> getBounds(TypeSolver typeSolver);

    class Bound {
        private boolean extendsBound;
        private Type type;

        private Bound(boolean extendsBound, Type type) {
            this.extendsBound = extendsBound;
            this.type = type;
        }

        public static Bound extendsBound(Type type) {
            return new Bound(true, type);
        }

        public static Bound superBound(Type type) {
            return new Bound(false, type);
        }

        public Type getType() {
            return type;
        }

        public boolean isExtends() {
            return extendsBound;
        }

        public boolean isSuper() {
            return !isExtends();
        }
    }

}
