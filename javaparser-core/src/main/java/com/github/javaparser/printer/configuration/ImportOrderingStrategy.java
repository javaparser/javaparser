package com.github.javaparser.printer.configuration;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.NodeList;

import java.util.List;

public interface ImportOrderingStrategy {

    List<NodeList<ImportDeclaration>> sortImports(NodeList<ImportDeclaration> nodes);

    void setSortImportsAlphabetically(boolean sortAlphabetically);

    boolean isSortImportsAlphabetically();

}
