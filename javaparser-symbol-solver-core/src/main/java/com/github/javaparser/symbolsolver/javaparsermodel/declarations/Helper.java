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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.*;

import java.util.EnumSet;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

/**
 * @author Federico Tomassetti
 */
class Helper {

    public static AccessSpecifier toAccessLevel(EnumSet<Modifier> modifiers) {
        if (modifiers.contains(Modifier.PRIVATE)) {
            return AccessSpecifier.PRIVATE;
        } else if (modifiers.contains(Modifier.PROTECTED)) {
            return AccessSpecifier.PROTECTED;
        } else if (modifiers.contains(Modifier.PUBLIC)) {
            return AccessSpecifier.PUBLIC;
        } else {
            return AccessSpecifier.DEFAULT;
        }
    }

    static String containerName(Node container) {
        String packageName = getPackageName(container);
        String className = getClassName("", container);
        return packageName +
                ((!packageName.isEmpty() && !className.isEmpty()) ? "." : "") +
                className;
    }

    static String getPackageName(Node container) {
        if (container instanceof CompilationUnit) {
            Optional<PackageDeclaration> p = ((CompilationUnit) container).getPackageDeclaration();
            if (p.isPresent()) {
                return p.get().getName().toString();
            }
        } else if (container != null) {
            return getPackageName(container.getParentNode().orElse(null));
        }
        return "";
    }

    static String getClassName(String base, Node container) {
        if (container instanceof com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) {
            String b = getClassName(base, container.getParentNode().orElse(null));
            String cn = ((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) container).getName().getId();
            if (b.isEmpty()) {
                return cn;
            } else {
                return b + "." + cn;
            }
        } else if (container instanceof com.github.javaparser.ast.body.EnumDeclaration) {
            String b = getClassName(base, container.getParentNode().orElse(null));
            String cn = ((com.github.javaparser.ast.body.EnumDeclaration) container).getName().getId();
            if (b.isEmpty()) {
                return cn;
            } else {
                return b + "." + cn;
            }
        } else if (container != null) {
            return getClassName(base, container.getParentNode().orElse(null));
        }
        return base;
    }
}
