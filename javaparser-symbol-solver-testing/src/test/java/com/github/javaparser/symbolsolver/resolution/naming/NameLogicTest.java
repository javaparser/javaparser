package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class NameLogicTest extends AbstractResolutionTest {

    private Node getNameInCode(String code, String name, ParseStart parseStart) {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_10);
        ParseResult<? extends Node> parseResult = new JavaParser(parserConfiguration).parse(parseStart, new StringProvider(code));
        if (!parseResult.isSuccessful()) {
            parseResult.getProblems().forEach(p -> System.out.println("ERR: " + p));
        }
        assertTrue(parseResult.isSuccessful());
        Node root = parseResult.getResult().get();
        List<Node> allNames = root.findAll(Node.class).stream()
                .filter(NameLogic::isAName)
                .collect(Collectors.toList());
        List<Node> matchingNames = allNames.stream()
                .filter(n -> NameLogic.nameAsString(n).equals(name))
                .collect(Collectors.toList());
        if (matchingNames.size() == 0) {
            throw new IllegalArgumentException("Not found. Names found: " + String.join(", ",
                    allNames.stream().map(NameLogic::nameAsString).collect(Collectors.toList())));
        } else if (matchingNames.size() > 1) {
            throw new IllegalArgumentException("Ambiguous");
        } else {
            return matchingNames.get(0);
        }
    }

    private void assertNameInCodeIsSyntactically(String code, String name, NameCategory nameCategory, ParseStart parseStart) {
        Node nameNode = getNameInCode(code, name, parseStart);
        assertEquals(nameCategory, NameLogic.syntacticClassificationAccordingToContext(nameNode));
    }

    @Test
    public void requiresModuleName() {
        assertNameInCodeIsSyntactically("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "java.xml", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void exportsModuleName() {
        assertNameInCodeIsSyntactically("module my.module{\n" +
                "  exports my.packag to other.module, another.module;\n" +
                "}", "other.module", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void opensModuleName() {
        assertNameInCodeIsSyntactically("module client.modul{\n" +
                "    opens some.client.packag to framework.modul;\n" +
                "    requires framework.modul2;\n" +
                "}", "framework.modul", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void exportsPackageName() {
        assertNameInCodeIsSyntactically("module common.widget{\n" +
                "  exports com.logicbig;\n" +
                "}", "com.logicbig", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void opensPackageName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example.bar", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void packageNameInPackageName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }
    
}
