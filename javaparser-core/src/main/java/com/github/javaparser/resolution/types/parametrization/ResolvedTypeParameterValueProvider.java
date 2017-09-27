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

package com.github.javaparser.resolution.types.parametrization;

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedWildcard;

import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public interface ResolvedTypeParameterValueProvider {

    /**
     * Calculate the value for the given type parameter.
     * It could be inherited.
     */
    Optional<ResolvedType> typeParamValue(ResolvedTypeParameterDeclaration typeParameterDeclaration);

    /**
     * Replace the type typeParametersValues present in the given type with the ones for which this type
     * has a value.
     */
    default ResolvedType useThisTypeParametersOnTheGivenType(ResolvedType type) {
        if (type.isTypeVariable()) {
            ResolvedTypeParameterDeclaration typeParameter = type.asTypeParameter();
            if (typeParameter.declaredOnType()) {
                Optional<ResolvedType> typeParam = typeParamValue(typeParameter);
                if (typeParam.isPresent()) {
                    type = typeParam.get();
                }
            }
        }

        if (type.isWildcard() && type.asWildcard().isBounded()) {
            if (type.asWildcard().isExtends()) {
                return ResolvedWildcard.extendsBound(useThisTypeParametersOnTheGivenType(type.asWildcard().getBoundedType()));
            } else {
                return ResolvedWildcard.superBound(useThisTypeParametersOnTheGivenType(type.asWildcard().getBoundedType()));
            }
        }

        if (type.isReferenceType()) {
            type = type.asReferenceType().transformTypeParameters(this::useThisTypeParametersOnTheGivenType);
        }

        return type;
    }

    Optional<ResolvedType> getGenericParameterByName(String name);
}
