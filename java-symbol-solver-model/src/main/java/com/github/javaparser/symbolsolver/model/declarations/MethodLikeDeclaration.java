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

import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

/**
 * This is a common interface for MethodDeclaration and ConstructorDeclaration.
 *
 * @author Federico Tomassetti
 */
public interface MethodLikeDeclaration extends Declaration, TypeParametrizable, HasAccessLevel {
    /**
     * The package name of the declaring type.
     */
    default String getPackageName() {
        return declaringType().getPackageName();
    }

    /**
     * The class(es) wrapping the declaring type.
     */
    default String getClassName() {
        return declaringType().getClassName();
    }

    /**
     * The qualified name of the method composed by the qualfied name of the declaring type
     * followed by a dot and the name of the method.
     */
    default String getQualifiedName() {
        return declaringType().getQualifiedName() + "." + this.getName();
    }

    /**
     * The signature of the method.
     */
    default String getSignature() {
        StringBuffer sb = new StringBuffer();
        sb.append(getName());
        sb.append("(");
        for (int i = 0; i < getNumberOfParams(); i++) {
            if (i != 0) {
                sb.append(", ");
            }
            sb.append(getParam(i).describeType());
        }
        sb.append(")");
        return sb.toString();
    }

    /**
     * The qualified signature of the method. It is composed by the qualified name of the declaring type
     * followed by the signature of the method.
     */
    default String getQualifiedSignature() {
        return declaringType().getId() + "." + this.getSignature();
    }

    /**
     * The type in which the method is declared.
     */
    ReferenceTypeDeclaration declaringType();

    /**
     * Number of params.
     */
    int getNumberOfParams();

    /**
     * Get the ParameterDeclaration at the corresponding position or throw IllegalArgumentException.
     */
    ParameterDeclaration getParam(int i);

    /**
     * Utility method to get the last ParameterDeclaration. It throws UnsupportedOperationException if the method
     * has no parameters.
     * The last parameter can be variadic and sometimes it needs to be handled in a special way.
     */
    default ParameterDeclaration getLastParam() {
        if (getNumberOfParams() == 0) {
            throw new UnsupportedOperationException("This method has no typeParametersValues, therefore it has no a last parameter");
        }
        return getParam(getNumberOfParams() - 1);
    }

    /**
     * Has the method or construcor a variadic parameter?
     * Note that when a method has a variadic parameter it should have an array type.
     */
    default boolean hasVariadicParameter() {
        if (getNumberOfParams() == 0) {
            return false;
        } else {
            return getParam(getNumberOfParams() - 1).isVariadic();
        }
    }

    @Override
    default Optional<TypeParameterDeclaration> findTypeParameter(String name) {
        for (TypeParameterDeclaration tp : this.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(tp);
            }
        }
        return declaringType().findTypeParameter(name);
    }

    /**
     * Number of exceptions listed in the throws clause.
     */
    int getNumberOfSpecifiedExceptions();

    /**
     * Type of the corresponding entry in the throws clause.
     *
     * @throws IllegalArgumentException if the index is negative or it is equal or greater than the value returned by
     *                                  getNumberOfSpecifiedExceptions
     * @throws UnsupportedOperationException for those types of methods of constructor that do not declare exceptions
     */
    Type getSpecifiedException(int index);

    default List<Type> getSpecifiedExceptions() {
        if (getNumberOfSpecifiedExceptions() == 0) {
            return Collections.emptyList();
        } else {
            List<Type> exceptions = new LinkedList<>();
            for (int i=0;i<getNumberOfSpecifiedExceptions();i++) {
                exceptions.add(getSpecifiedException(i));
            }
            return exceptions;
        }
    }
}
