package com.github.javaparser.printer.configuration.imports;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class IntelliJImportOrderingStrategyTest {

    private final IntelliJImportOrderingStrategy strategy = new IntelliJImportOrderingStrategy();

    @Test
    void sortImports_givenNoImports_ThenNoImports_ShouldBeReturned() {
        List<NodeList<ImportDeclaration>> actual = strategy.sortImports(new NodeList<>());
        assertEquals(3, actual.size());
        assertEquals(0, actual.get(0).size());
        assertEquals(0, actual.get(1).size());
        assertEquals(0, actual.get(2).size());
    }

    @Test
    void sortImports_givenImports_ThenImportsShouldBeInCorrectLocation() {

        NodeList<ImportDeclaration> imports = new NodeList<>();
        imports.add(new ImportDeclaration("org.junit.jupiter.api.Assertions.assertEquals", true, false));
        imports.add(new ImportDeclaration("java.util.List", false, false));
        imports.add(new ImportDeclaration("com.example.Test", false, false));

        List<NodeList<ImportDeclaration>> actual = strategy.sortImports(imports);
        assertEquals(3, actual.size());

        assertEquals(1, actual.get(0).size());
        assertEquals("com.example.Test", actual.get(0).get(0).getNameAsString());

        assertEquals(1, actual.get(1).size());
        assertEquals("java.util.List", actual.get(1).get(0).getNameAsString());

        assertEquals(1, actual.get(2).size());
        assertEquals("org.junit.jupiter.api.Assertions.assertEquals", actual.get(2).get(0).getNameAsString());
    }

    @Test
    void sortImports_givenUnsortedImportsAndSortingIsTrue_ThenImportsShouldBeSorted() {
        NodeList<ImportDeclaration> imports = new NodeList<>();
        imports.add(new ImportDeclaration("com.example.B", false, false));
        imports.add(new ImportDeclaration("com.example.A", false, false));

        strategy.setSortImportsAlphabetically(true);

        List<NodeList<ImportDeclaration>> actual = strategy.sortImports(imports);
        assertEquals(3, actual.size());

        assertEquals(2, actual.get(0).size());
        assertEquals("com.example.A", actual.get(0).get(0).getNameAsString());
        assertEquals("com.example.B", actual.get(0).get(1).getNameAsString());
        assertEquals(0, actual.get(1).size());
        assertEquals(0, actual.get(2).size());
    }

}