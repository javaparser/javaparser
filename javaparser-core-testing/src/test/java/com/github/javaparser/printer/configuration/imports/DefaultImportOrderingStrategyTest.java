package com.github.javaparser.printer.configuration.imports;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class DefaultImportOrderingStrategyTest {

    private final DefaultImportOrderingStrategy strategy = new DefaultImportOrderingStrategy();

    @Test
    void sortImports_givenNoImports_ThenNoImports_ShouldBeReturned() {
        List<NodeList<ImportDeclaration>> actual = strategy.sortImports(new NodeList<>());
        assertEquals(1, actual.size());
        assertEquals(0, actual.get(0).size());
    }

    @Test
    void sortImports_givenImports_ThenImportsShouldBeInCorrectLocation() {

        NodeList<ImportDeclaration> imports = new NodeList<>();
        imports.add(new ImportDeclaration("org.junit.jupiter.api.Assertions.assertEquals", true, false));
        imports.add(new ImportDeclaration("java.util.List", false, false));
        imports.add(new ImportDeclaration("com.example.Test", false, false));

        List<NodeList<ImportDeclaration>> actual = strategy.sortImports(imports);
        assertEquals(1, actual.size());

        NodeList<ImportDeclaration> actualImports = actual.get(0);

        assertEquals(3, actualImports.size());
        assertEquals("org.junit.jupiter.api.Assertions.assertEquals", actualImports.get(0).getNameAsString());
        assertEquals("java.util.List", actualImports.get(1).getNameAsString());
        assertEquals("com.example.Test", actualImports.get(2).getNameAsString());
    }

    @Test
    void sortImports_givenUnsortedImportsAndSortingIsTrue_ThenImportsShouldBeSorted() {
        NodeList<ImportDeclaration> imports = new NodeList<>();
        imports.add(new ImportDeclaration("com.example.B", false, false));
        imports.add(new ImportDeclaration("com.example.A", false, false));

        strategy.setSortImportsAlphabetically(true);

        List<NodeList<ImportDeclaration>> actual = strategy.sortImports(imports);
        assertEquals(1, actual.size());

        NodeList<ImportDeclaration> actualImports = actual.get(0);

        assertEquals(2, actualImports.size());
        assertEquals("com.example.A", actualImports.get(0).getNameAsString());
        assertEquals("com.example.B", actualImports.get(1).getNameAsString());
    }

}