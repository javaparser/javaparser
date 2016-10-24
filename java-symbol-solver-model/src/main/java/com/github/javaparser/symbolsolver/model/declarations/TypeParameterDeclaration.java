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

package com.github.javaparser.symbolsolver.model.declarations;

import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.util.List;

/**
 * Declaration of a type parameter.
 * For example:
 * <p>
 *     class A&lt;E extends String&gt;{}
 * </p>
 *
 * In this case <b>E</b> would be a type parameter.
 *
 * @author Federico Tomassetti
 */
public interface TypeParameterDeclaration {

    /**
     * Instantiate a TypeParameter defined on a Type with the given data.
     */
    static TypeParameterDeclaration onType(final String name, String classQName, List<Bound> bounds) {
        return new TypeParameterDeclaration() {
            @Override
            public String getName() {
                return name;
            }

            @Override
            public boolean declaredOnType() {
                return true;
            }

            @Override
            public boolean declaredOnMethod() {
                return false;
            }

            @Override
            public String getContainerQualifiedName() {
                return classQName;
            }

            @Override
            public String getContainerId() {
                return classQName;
            }

            @Override
            public List<Bound> getBounds(TypeSolver typeSolver) {
                return bounds;
            }

            @Override
            public String toString() {
                return "TypeParameter onType " + name;
            }
        };
    }

    /**
     * Name of the type parameter.
     */
    String getName();

    /**
     * Is the type parameter been defined on a type?
     */
    boolean declaredOnType();

    /**
     * Is the type parameter been defined on a method?
     */
    boolean declaredOnMethod();

    /**
     * The qualified name of the Type Parameter.
     * It is composed by the qualified name of the container followed by a dot and the name of the Type Parameter.
     * The qualified name of a method is its qualified signature.
     */
    default String getQualifiedName() {
        return String.format("%s.%s", getContainerId(), getName());
    }

    /**
     * The qualified name of the container.
     */
    String getContainerQualifiedName();

    /**
     * The ID of the container. See TypeContainer.getId
     */
    String getContainerId();

    /**
     * The bounds specified for the type parameter.
     * For example:
     * "extends A" or "super B"
     */
    List<Bound> getBounds(TypeSolver typeSolver);

    /**
     * A Bound on a Type Parameter.
     */
    class Bound {
        private boolean extendsBound;
        private Type type;

        private Bound(boolean extendsBound, Type type) {
            this.extendsBound = extendsBound;
            this.type = type;
        }

        /**
         * Create an extends bound with the given type:
         * <p>
         *     extends "given type"
         * </p>
         */
        public static Bound extendsBound(Type type) {
            return new Bound(true, type);
        }

        /**
         * Create a super bound with the given type:
         * <p>
         *     super "given type"
         * </p>
         */
        public static Bound superBound(Type type) {
            return new Bound(false, type);
        }

        /**
         * Get the type used in the Bound.
         */
        public Type getType() {
            return type;
        }

        /**
         * Is this an extends bound?
         */
        public boolean isExtends() {
            return extendsBound;
        }

        /**
         * Is this a super bound?
         */
        public boolean isSuper() {
            return !isExtends();
        }
    }

}
