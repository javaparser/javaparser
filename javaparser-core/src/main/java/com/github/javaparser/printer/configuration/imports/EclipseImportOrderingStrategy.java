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

public class EclipseImportOrderingStrategy implements ImportOrderingStrategy {

    private boolean sortImportsAlphabetically = false;

    @Override
    public List<NodeList<ImportDeclaration>> sortImports(NodeList<ImportDeclaration> nodes) {
        NodeList<ImportDeclaration> staticImports = new NodeList<>();
        NodeList<ImportDeclaration> javaImports = new NodeList<>();
        NodeList<ImportDeclaration> javaXImports = new NodeList<>();
        NodeList<ImportDeclaration> orgImports = new NodeList<>();
        NodeList<ImportDeclaration> comImports = new NodeList<>();
        NodeList<ImportDeclaration> otherImports = new NodeList<>();
        for (ImportDeclaration importDeclaration : nodes) {
            // Check if is a static import
            if (importDeclaration.isStatic()) {
                staticImports.add(importDeclaration);
                continue;
            }
            String importName = importDeclaration.getNameAsString();
            if (importName.startsWith("java.")) {
                javaImports.add(importDeclaration);
            } else if (importName.startsWith("javax.")) {
                javaXImports.add(importDeclaration);
            } else if (importName.startsWith("org.")) {
                orgImports.add(importDeclaration);
            } else if (importName.startsWith("com.")) {
                comImports.add(importDeclaration);
            } else {
                otherImports.add(importDeclaration);
            }
        }
        if (sortImportsAlphabetically) {
            Comparator<ImportDeclaration> sortLogic = Comparator.comparing(NodeWithName::getNameAsString);
            staticImports.sort(sortLogic);
            javaImports.sort(sortLogic);
            javaXImports.sort(sortLogic);
            orgImports.sort(sortLogic);
            comImports.sort(sortLogic);
            otherImports.sort(sortLogic);
        }
        return Arrays.asList(staticImports, javaImports, javaXImports, orgImports, comImports, otherImports);
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
