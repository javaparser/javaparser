/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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
package com.github.javaparser.printer.configuration.imports;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.printer.configuration.ImportOrderingStrategy;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

public class IntelliJImportOrderingStrategy implements ImportOrderingStrategy {

    private boolean sortImportsAlphabetically = false;

    @Override
    public List<NodeList<ImportDeclaration>> sortImports(NodeList<ImportDeclaration> nodes) {
        NodeList<ImportDeclaration> otherImports = new NodeList<>();
        NodeList<ImportDeclaration> javaImports = new NodeList<>();
        NodeList<ImportDeclaration> staticImports = new NodeList<>();
        for (ImportDeclaration importDeclaration : nodes) {
            // Check if is a static import
            if (importDeclaration.isStatic()) {
                staticImports.add(importDeclaration);
                continue;
            }
            String importName = importDeclaration.getNameAsString();
            if (importName.startsWith("java.") || importName.startsWith("javax.")) {
                javaImports.add(importDeclaration);
            } else {
                otherImports.add(importDeclaration);
            }
        }
        if (sortImportsAlphabetically) {
            Comparator<ImportDeclaration> sortLogic = Comparator.comparing(NodeWithName::getNameAsString);
            otherImports.sort(sortLogic);
            javaImports.sort(sortLogic);
            staticImports.sort(sortLogic);
        }
        return Arrays.asList(otherImports, javaImports, staticImports);
    }

    @Override
    public void setSortImportsAlphabetically(boolean sortAlphabetically) {
        sortImportsAlphabetically = sortAlphabetically;
    }

    @Override
    public boolean isSortImportsAlphabetically() {
        return sortImportsAlphabetically;
    }
}
