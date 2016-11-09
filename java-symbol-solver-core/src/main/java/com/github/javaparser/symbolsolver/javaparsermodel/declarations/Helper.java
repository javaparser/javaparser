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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.AccessLevel;

import java.util.EnumSet;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

/**
 * @author Federico Tomassetti
 */
class Helper {

    public static AccessLevel toAccessLevel(EnumSet<Modifier> modifiers) {
        if (modifiers.contains(Modifier.PRIVATE)) {
            return AccessLevel.PRIVATE;
        } else if (modifiers.contains(Modifier.PROTECTED)) {
            return AccessLevel.PROTECTED;
        } else if (modifiers.contains(Modifier.PUBLIC)) {
            return AccessLevel.PUBLIC;
        } else {
            return AccessLevel.PACKAGE_PROTECTED;
        }
    }

    public static String containerName(String base, Node container) {
        if (container instanceof com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) {
            String b = containerName(base, getParentNode(container));
            String cn = ((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) container).getName();
            if (b.isEmpty()) {
                return cn;
            } else {
                return b + "." + cn;
            }
        } else if (container instanceof CompilationUnit) {
            PackageDeclaration p = ((CompilationUnit) container).getPackage();
            if (p != null) {
                String b = p.getName().toString();
                if (base.isEmpty()) {
                    return b;
                } else {
                    return b + "." + base;
                }
            } else {
                return base;
            }
        } else if (container != null) {
            return containerName(base, getParentNode(container));
        } else {
            return base;
        }
    }
}
