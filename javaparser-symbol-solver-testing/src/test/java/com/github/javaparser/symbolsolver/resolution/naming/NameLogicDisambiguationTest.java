package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.*;
import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class NameLogicDisambiguationTest extends AbstractNameLogicTest {

    private void assertNameInCodeIsDisambiguited(String code, String name,
                                                 NameCategory syntacticClassification,
                                                 NameCategory nameCategory,
                                                 ParseStart parseStart, TypeSolver typeSolver) {
        Node nameNode = getNameInCodeTollerant(code, name, parseStart);
        assertEquals(syntacticClassification, NameLogic.syntacticClassificationAccordingToContext(nameNode));
        assertEquals(nameCategory, NameLogic.classifyReference(nameNode, typeSolver));
    }

    @Test
    public void ambiguousNameToLocalVar() {
        assertNameInCodeIsDisambiguited("class A { void foo() {\n" +
                "SomeClass a; a.aField;" + "\n" +
                "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new ReflectionTypeSolver());
    }

}
