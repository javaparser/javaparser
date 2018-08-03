package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.*;
import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
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
        Node nameNode = getNameInCodeTollerant(code, name, parseStart, typeSolver);
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

    @Test
    public void ambiguousNameToLocalVarInAnnidatedBlocks() {
        assertNameInCodeIsDisambiguited("class A { void foo() {{\n" +
                        "SomeClass a; {{a.aField;}}}" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new ReflectionTypeSolver());
    }

    @Test
    public void ambiguousNameToLocalVarFromOldFor() {
        assertNameInCodeIsDisambiguited("class A { void foo() {\n" +
                        "for (SomeClass a=null;true;){ a.aField; }" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new ReflectionTypeSolver());
    }

    @Test
    public void ambiguousNameToLocalVarFromNewFor() {
        assertNameInCodeIsDisambiguited("class A { void foo() {\n" +
                        "for (SomeClass a : null){ a.aField; }" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new ReflectionTypeSolver());
    }

    @Test
    public void ambiguousNameToLocalVarFromTryWithResource() {
        assertNameInCodeIsDisambiguited("class A { void foo() {\n" +
                        "try (SomeClass a = null){ a.aField; }" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new ReflectionTypeSolver());
    }

    @Test
    public void ambiguousNameToMethodParameter() {
        assertNameInCodeIsDisambiguited("class A { void foo(SomeClass a) {\n" +
                        "a.aField;" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new ReflectionTypeSolver());
    }

    @Test
    public void ambiguousNameToCatchParameter() {
        assertNameInCodeIsDisambiguited("class A { void foo() {\n" +
                        "try { } catch (SomeClass a) { a.aField; }" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new ReflectionTypeSolver());
    }

    @Test
    public void ambiguousNameToInstanceFieldDeclared() {
        assertNameInCodeIsDisambiguited("class A { SomeClass a; void foo() {\n" +
                        "a.aField;" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new CombinedTypeSolver(new ReflectionTypeSolver()));
    }

    @Test
    public void ambiguousNameToStaticFieldDeclared() {
        assertNameInCodeIsDisambiguited("class A { static SomeClass a; void foo() {\n" +
                        "a.aField;" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new CombinedTypeSolver(new ReflectionTypeSolver()));
    }

    @Test
    public void ambiguousNameToInstanceFieldInherited() {
        assertNameInCodeIsDisambiguited("class A { SomeClass a; } class B extends A { void foo() {\n" +
                        "a.aField;" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new CombinedTypeSolver(new ReflectionTypeSolver()));
    }

    @Test
    public void ambiguousNameToStaticFieldInherited() {
        assertNameInCodeIsDisambiguited("class A { static SomeClass a; } class B extends A {  void foo() {\n" +
                        "a.aField;" + "\n" +
                        "} }", "a", NameCategory.AMBIGUOUS_NAME, NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT,
                new CombinedTypeSolver(new ReflectionTypeSolver()));
    }

    // Otherwise, if a field of that name is declared in the compilation unit (§7.3) containing the Identifier by a
    // single-static-import declaration (§7.5.3), or by a static-import-on-demand declaration (§7.5.4) then the
    // AmbiguousName is reclassified as an ExpressionName.

}
