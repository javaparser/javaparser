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
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import static java.util.Comparator.comparingInt;

public class DefaultImportOrderingStrategy implements ImportOrderingStrategy {

    private boolean sortImportsAlphabetically = false;

    @Override
    public List<NodeList<ImportDeclaration>> sortImports(NodeList<ImportDeclaration> nodes) {
        if (sortImportsAlphabetically) {
            Comparator<ImportDeclaration> sortLogic = comparingInt((ImportDeclaration i) -> i.isStatic() ? 0 : 1).thenComparing(NodeWithName::getNameAsString);
            nodes.sort(sortLogic);
        }
        return Collections.singletonList(nodes);
    }

    @Override
    public void setSortImportsAlphabetically(boolean sortImportsAlphabetically) {
        this.sortImportsAlphabetically = sortImportsAlphabetically;
    }

    @Override
    public boolean isSortImportsAlphabetically() {
        return sortImportsAlphabetically;
    }
}
