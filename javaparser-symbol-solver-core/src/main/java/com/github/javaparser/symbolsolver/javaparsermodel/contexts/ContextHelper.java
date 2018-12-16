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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
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
        } else {
            throw new UnsupportedOperationException(typeDeclaration.toString());
        }
    }
}
