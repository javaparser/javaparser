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

package me.tomassetti.symbolsolver.core.resolution;

import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import me.tomassetti.symbolsolver.javassistmodel.JavassistMethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionMethodDeclaration;

import java.util.List;

public class ContextHelper {

    static MethodUsage resolveTypeVariables(Context context, MethodDeclaration methodDeclaration, List<Type> parameterTypes) {
        if (methodDeclaration instanceof JavaParserMethodDeclaration) {
            return ((JavaParserMethodDeclaration)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else if (methodDeclaration instanceof JavassistMethodDeclaration) {
            return ((JavassistMethodDeclaration)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else if (methodDeclaration instanceof JavaParserEnumDeclaration.ValuesMethod) {
            return ((JavaParserEnumDeclaration.ValuesMethod)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else if (methodDeclaration instanceof ReflectionMethodDeclaration) {
            return ((ReflectionMethodDeclaration)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else {
            throw new UnsupportedOperationException();
        }
    }
}
