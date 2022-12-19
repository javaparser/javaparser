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
            Comparator<ImportDeclaration> sortLogic = comparingInt((ImportDeclaration i) -> i.isStatic() ? 0 : 1)
                    .thenComparing(NodeWithName::getNameAsString);
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
