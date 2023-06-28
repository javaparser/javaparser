/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;

import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class ContextHelper {

    private ContextHelper() {
        // prevent instantiation
    }

    public static Optional<MethodUsage> solveMethodAsUsage(ResolvedTypeDeclaration typeDeclaration, String name,
                                                           List<ResolvedType> argumentsTypes, Context invokationContext,
                                                           List<ResolvedType> typeParameters) {

        if (typeDeclaration instanceof MethodUsageResolutionCapability) {
            return ((MethodUsageResolutionCapability) typeDeclaration)
                           .solveMethodAsUsage(name, argumentsTypes, invokationContext, typeParameters);
        }
        throw new UnsupportedOperationException(typeDeclaration.toString());
    }
}
