/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.resolution.declarations;


import com.github.javaparser.resolution.types.ResolvedType;

import java.util.List;
import java.util.Optional;

/**
 * Declaration of a type parameter.
 * For example:
 * <p>
 * class A&lt;E extends String&gt;{}
 * </p>
 * <p>
 * In this case <b>E</b> would be a type parameter.
 *
 * @author Federico Tomassetti
 */
public interface ResolvedTypeParameterDeclaration extends ResolvedTypeDeclaration {

    /**
     * Instantiate a TypeParameter defined on a Type with the given data.
     */
    static ResolvedTypeParameterDeclaration onType(final String name, String classQName, List<Bound> bounds) {
        return new ResolvedTypeParameterDeclaration() {
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
            public boolean declaredOnConstructor() {
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
            public ResolvedTypeParametrizable getContainer() {
                return null;
            }

            @Override
            public List<Bound> getBounds() {
                return bounds;
            }

            @Override
            public String toString() {
                return "TypeParameter onType " + name;
            }

            @Override
            public Optional<ResolvedReferenceTypeDeclaration> containerType() {
                throw new UnsupportedOperationException();
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
    default boolean declaredOnType() {
        return (getContainer() instanceof ResolvedReferenceTypeDeclaration);
    }

    /**
     * Is the type parameter been defined on a method?
     */
    default boolean declaredOnMethod() {
        return (getContainer() instanceof ResolvedMethodDeclaration);
    }

    /**
     * Is the type parameter been defined on a constructor?
     */
    default boolean declaredOnConstructor() {
        return (getContainer() instanceof ResolvedConstructorDeclaration);
    }

    /**
     * The package name of the type bound(s).
     * This is unsupported because there is no package for a Type Parameter, only for its container.
     */
    default String getPackageName() {
        throw new UnsupportedOperationException();
    }

    /**
     * The class(es) wrapping the type bound(s).
     * This is unsupported because there is no class for a Type Parameter, only for its container.
     */
    default String getClassName() {
        throw new UnsupportedOperationException();
    }

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
     * The TypeParametrizable of the container. Can be either a ReferenceTypeDeclaration or a MethodLikeDeclaration
     */
    ResolvedTypeParametrizable getContainer();

    /**
     * The bounds specified for the type parameter.
     * For example:
     * "extends A" or "super B"
     */
    List<Bound> getBounds();

    /**
     * Has the type parameter a lower bound?
     */
    default boolean hasLowerBound() {
        for (Bound b : getBounds()) {
            if (b.isExtends()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Has the type parameter an upper bound?
     */
    default boolean hasUpperBound() {
        for (Bound b : getBounds()) {
            if (b.isSuper()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Get the type used as lower bound.
     *
     * @throws IllegalStateException if there is no lower bound
     */
    default ResolvedType getLowerBound() {
        for (Bound b : getBounds()) {
            if (b.isExtends()) {
                return b.getType();
            }
        }
        throw new IllegalStateException();
    }

    /**
     * Get the type used as upper bound.
     *
     * @throws IllegalStateException if there is no upper bound
     */
    default ResolvedType getUpperBound() {
        for (Bound b : getBounds()) {
            if (b.isSuper()) {
                return b.getType();
            }
        }
        throw new IllegalStateException();
    }

    /**
     * A Bound on a Type Parameter.
     */
    class Bound {
        private boolean extendsBound;
        private ResolvedType type;

        private Bound(boolean extendsBound, ResolvedType type) {
            this.extendsBound = extendsBound;
            this.type = type;
        }

        /**
         * Create an extends bound with the given type:
         * <p>
         * extends "given type"
         * </p>
         */
        public static Bound extendsBound(ResolvedType type) {
            return new Bound(true, type);
        }

        /**
         * Create a super bound with the given type:
         * <p>
         * super "given type"
         * </p>
         */
        public static Bound superBound(ResolvedType type) {
            return new Bound(false, type);
        }

        /**
         * Get the type used in the Bound.
         */
        public ResolvedType getType() {
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

        @Override
        public String toString() {
            return "Bound{" +
                    "extendsBound=" + extendsBound +
                    ", type=" + type +
                    '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Bound bound = (Bound) o;

            if (extendsBound != bound.extendsBound) return false;
            return type != null ? type.equals(bound.type) : bound.type == null;
        }

        @Override
        public int hashCode() {
            int result = (extendsBound ? 1 : 0);
            result = 31 * result + (type != null ? type.hashCode() : 0);
            return result;
        }
    }

}
