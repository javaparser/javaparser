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
package com.github.javaparser.printer.configuration;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.NodeList;
import java.util.List;

public interface ImportOrderingStrategy {

    /**
     * Sort the list of imports into groups.
     *
     * <p>
     *
     * Consider that we have the following list of imports as argument:
     * <br>
     * <pre>
     * import java.util.List;
     * import com.github.javaparser.ast.NodeList;
     * import com.github.javaparser.ast.ImportDeclaration;
     * </pre>
     *
     * <p>
     *
     * And we want the imports to look like this: (Note the spacing between imports)
     * <pre>
     * import java.util.List;
     *
     * import com.github.javaparser.ast.NodeList;
     * import com.github.javaparser.ast.ImportDeclaration;
     * </pre>
     *
     * <p>
     *
     * In this case, we have two groups of imports. The first group contains only import for java.util.List,
     * while the second group contains NodeList and ImportDeclaration.
     * <p>
     * For this example this method should return 2 groups in the list, and the first group should have
     * exactly 1 import, while the second group should have 2 imports.
     *
     * @param imports The imports to be ordered.
     *
     * @return The group of sorted imports.
     */
    List<NodeList<ImportDeclaration>> sortImports(NodeList<ImportDeclaration> imports);

    void setSortImportsAlphabetically(boolean sortAlphabetically);

    boolean isSortImportsAlphabetically();
}
