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

package com.github.javaparser.ast.body;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.opentest4j.AssertionFailedError;

import java.util.List;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.*;

public class RecordDeclarationTest {

    @Nested
    class LanguageLevels {
        @ParameterizedTest
        @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_13", "JAVA_13_PREVIEW", "JAVA_14", "JAVA_15"})
        void basicGrammarCompiles_languageLevelValidation_forbidden(ParserConfiguration.LanguageLevel languageLevel) {
            String s = "record Point(int x, int y) { }";
            assertThrows(AssertionFailedError.class, () -> {
                CompilationUnit cu = TestParser.parseCompilationUnit(languageLevel, s);
            });
        }

        @ParameterizedTest
        @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_14_PREVIEW", "JAVA_15_PREVIEW", "JAVA_16", "JAVA_16_PREVIEW"})
        void basicGrammarCompiles_languageLevelValidation_permitted(ParserConfiguration.LanguageLevel languageLevel) {
            String s = "record Point(int x, int y) { }";
            CompilationUnit cu = TestParser.parseCompilationUnit(languageLevel, s);
        }

        @ParameterizedTest
        @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_14_PREVIEW", "JAVA_15_PREVIEW", "JAVA_16", "JAVA_16_PREVIEW"})
        void languageLevelValidation_recordAsTypeIdentifier_permitted(ParserConfiguration.LanguageLevel languageLevel) {
            String s = "class record {}";
            assertThrows(AssertionFailedError.class, () -> {
                CompilationUnit cu = TestParser.parseCompilationUnit(languageLevel, s);
            });
        }

        @ParameterizedTest
        @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_13", "JAVA_13_PREVIEW", "JAVA_14", "JAVA_15"})
        void languageLevelValidation_recordAsTypeIdentifier_forbidden(ParserConfiguration.LanguageLevel languageLevel) {
            String s = "class record {}";
            CompilationUnit cu = TestParser.parseCompilationUnit(languageLevel, s);
        }
    }

    /**
     * https://openjdk.java.net/jeps/395#Description
     */
    @Test
    void basicGrammarCompiles() {
        String s = "record Point(int x, int y) { }";
        assertOneRecordDeclaration(TestParser.parseCompilationUnit(s));
    }

    /**
     * https://openjdk.java.net/jeps/395#Description
     */
    @Test
    void basicGrammar() {
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        RecordDeclaration recordDeclaration = cu.findAll(RecordDeclaration.class).get(0);

        assertTrue(recordDeclaration.isRecordDeclaration());
        assertTrue(recordDeclaration.getImplementedTypes().isEmpty());
        assertTrue(recordDeclaration.getTypeParameters().isEmpty());
        assertTrue(recordDeclaration.getFullyQualifiedName().isPresent());
        assertEquals("Point", recordDeclaration.getFullyQualifiedName().get());
        assertTrue(recordDeclaration.isRecordDeclaration());

        NodeList<Parameter> parameters = recordDeclaration.getParameters();
        assertEquals(2, parameters.size());

        Parameter parameter0 = parameters.get(0);
        assertEquals("x", parameter0.getNameAsString());
        assertEquals("int", parameter0.getTypeAsString());
        Parameter parameter1 = parameters.get(1);
        assertEquals("y", parameter1.getNameAsString());
        assertEquals("int", parameter1.getTypeAsString());

        assertEquals(0, recordDeclaration.getMembers().size());
    }

    /**
     * https://openjdk.java.net/jeps/395#Description
     */
    @Test
    void basicRecordPrints() {
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        String expected = "" +
                "record Point(int x, int y) {\n" +
                "}\n" +
                "";
        assertEqualsStringIgnoringEol(expected, cu.toString());
    }

    @Test
    void genericRecordPrints() {
        String s = "record Point<X,Y>(X x, Y y) { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        String expected = "" +
                "record Point<X, Y>(X x, Y y) {\n" +
                "}\n" +
                "";
        assertEqualsStringIgnoringEol(expected, cu.toString());
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-record
     */
    @Test
    void record_cannotExtend() {
        String s = "record Point(int x, int y) extends OtherThing { }";
        assertCompilationFails(s);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_cannotBeAbstract() {
        String s = "abstract record Point(int x, int y) { }";
        assertCompilationFails(s);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_mayImplementInterfaces() {
        String s = "record Point(int x, int y) implements OtherInterface { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);

        assertOneRecordDeclaration(cu);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_mayBeStatic() {
        String s = "static record Point(int x, int y) { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);

        assertOneRecordDeclaration(cu);
    }

    @Test
    void recordWithVarArgs() {
        String s = "record R(T1 c1, Tn... cn){ }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());

        RecordDeclaration recordDeclaration = recordDeclarations.get(0);
        NodeList<Parameter> parameters = recordDeclaration.getParameters();
        assertEquals(2, parameters.size());

        Parameter parameter0 = parameters.get(0);
        assertEquals("c1", parameter0.getNameAsString());
        assertEquals("T1", parameter0.getTypeAsString());
        assertFalse(parameter0.isVarArgs());

        Parameter parameter1 = parameters.get(1);
        assertEquals("cn", parameter1.getNameAsString());
        assertEquals("Tn", parameter1.getTypeAsString());
        assertTrue(parameter1.isVarArgs());
    }

    @Test
    void recordWithAnnotationedParameters() {
        String s = "record Card(@MyAnno Rank rank, @MyAnno Suit suit) { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());

        RecordDeclaration recordDeclaration = recordDeclarations.get(0);
        NodeList<Parameter> parameters = recordDeclaration.getParameters();
        assertEquals(2, parameters.size());

        Parameter parameter0 = parameters.get(0);
        assertEquals("rank", parameter0.getNameAsString());
        assertEquals("Rank", parameter0.getTypeAsString());
        assertEquals(1, parameter0.getAnnotations().size());

        Parameter parameter1 = parameters.get(1);
        assertEquals("suit", parameter1.getNameAsString());
        assertEquals("Suit", parameter1.getTypeAsString());
        assertEquals(1, parameter1.getAnnotations().size());

        assertEquals(0, recordDeclaration.getMembers().size());
    }

    @Test
    void record_emptyMembers() {
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        RecordDeclaration recordDeclaration = recordDeclarations.get(0);

        assertEquals(0, recordDeclaration.getMembers().size());
    }

    @Test
    void record_permitStaticMethods() {
        String s = "" +
                "record ABC(int x, int y) {\n" +
                "\n" +
                "    static public int abc() {\n" +
                "        return x;\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    @Test
    void record_permitMethods() {
        String s = "" +
                "record ABC(int x, int y) {\n" +
                "\n" +
                "    public int x() {\n" +
                "        return x;\n" +
                "    }\n" +
                "\n" +
                "    public String xyz() {\n" +
                "        return \"10\";\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    @Test
    void record_forbidNonStaticFields() {
        String s = "record Point(int x, int y) { int z; }";
        assertCompilationFails(s);
    }

    @Test
    void record_permitStaticFields() {
        String s = "record Point(int x, int y) { static int z; }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    @Test
    void record_permitPublicStaticFieldInRecord1() {
        String s = "public final record RecordPublicField() {" +
                   "  public static final Object EMPTY = new Object();" +
                   "}\n";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    @Test
    void record_permitPublicStaticFieldInNestedRecord() {
        String s = "public final record RecordTopLevel(Object member) {\n" +
                   "    private static record RecordNested() {\n" +
                   "        public static final RecordNested EMPTY = new RecordNested();\n" +
                   "    }\n" +
                   "}\n";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertTwoRecordDeclarations(cu);
    }

    @Test
    void record_permitStaticFields2() {
        String s = "" +
                "record ABC(int x, int y) {\n" +
                "\n" +
                "    static int z;\n" +
                "\n" +
                "    static {\n" +
                "        int z = 10;\n" +
                "    }\n" +
                "\n" +
                "    public int x() {\n" +
                "        return x;\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_isImplicitlyFinal() {
        String s = "record Point(int x, int y) { static int z; }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertFalse(recordDeclaration.hasModifier(Modifier.Keyword.FINAL));
        assertTrue(recordDeclaration.isFinal(), "Records are implicitly final.");
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_isImplicitlyFinalWithoutExplicit() {
        String s = "record Point(int x, int y) { static int z; }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertFalse(recordDeclaration.hasModifier(Modifier.Keyword.FINAL));
        assertTrue(recordDeclaration.isFinal(), "Records are implicitly final.");
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_canHaveGenerics() {
        String s = "record Point <T> (T x, int y) { }";
        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertFalse(recordDeclaration.getTypeParameters().isEmpty());
        assertEquals("T", recordDeclaration.getTypeParameters().get(0).getNameAsString());
    }


    @Test
    void record_mustNotAllowMismatchedComponentAccessorReturnType() {
        String s = "record Point(int x, int y) {\n" +
                "    public String x() {\n" +
                "        return \"10\";\n" +
                "    }\n" +
                "}";
        assertCompilationFails(s);
    }

    @Test
    void record_allowMethodsWithSameNameAsRecordComponentButNotAnAccessorMethod() {
        String s = "record Point(int x, int y) {\n" +
                "    public String x(int a) {\n" +
                "        return \"10\";\n" +
                "    }\n" +
                "}";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    @Test
    void record_allowMethodsWithSameNameAsRecordComponentButNotAnAccessorMethod2() {
        String s = "record Point(int x, int y) {\n" +
                "    public int x(int a) {\n" +
                "        return 10;\n" +
                "    }\n" +
                "}";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    @Test
    void record_allowComponentAccessorWithMatchingType() {
        String s = "record Point(int x, int y) {\n" +
                "    public int x() {\n" +
                "        return 10;\n" +
                "    }\n" +
                "}";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_allowNestedWithinClass() {
        String s = "\n" +
                "class X {\n" +
                "    record Point(int x, int y) {\n" +
                "    }\n" +
                "}\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_componentsAreImplicitlyFinal() {
        String s = "record Point(int x, int y) { }";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        RecordDeclaration recordDeclaration = cu.findAll(RecordDeclaration.class).get(0);

        NodeList<Parameter> parameters = recordDeclaration.getParameters();
        assertTrue(parameters.get(0).isFinal());
        assertTrue(parameters.get(1).isFinal());
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_allowClassWithinRecord() {
        String s = "\n" +
                "record Point(int x, int y) {\n" +
                "    class X {\n" +
                "    }\n" +
                "}\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());

        RecordDeclaration recordDeclaration = recordDeclarations.get(0);
        BodyDeclaration<?> member = recordDeclaration.getMember(0);

        assertTrue(member.isClassOrInterfaceDeclaration());
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_allowNestedWithinInterface() {
        String s = "\n" +
                "interface X {\n" +
                "    record Point(int x, int y) {\n" +
                "    }\n" +
                "}\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_allowNestedWithinEnum() {
        String s = "\n" +
                "enum ABC {\n" +
                "    ABC;\n" +
                "    \n" +
                "    record Point(int x, int y) {\n" +
                "    }\n" +
                "}\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_allowNestedMultiple() {
        String s = "\n" +
                "interface Y {\n" +
                "    class X {\n" +
                "        record Point(int x, int y) {\n" +
                "        }\n" +
                "    }\n" +
                "}\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_allowNestedMultiple2() {
        String s = "\n" +
                "interface Y {\n" +
                "    class X {\n" +
                "        record Point(int x, int y) {\n" +
                "        }\n" +
                "        record PointB(int x, int y) {\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    record PointC(int x, int y) {\n" +
                "    }\n" +
                "}\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(3, recordDeclarations.size());
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_topLevelRecordsAreNotStatic() {
        String s = "record Point(int x, int y) { }\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        RecordDeclaration recordDeclaration = cu.findAll(RecordDeclaration.class).get(0);
        assertFalse(recordDeclaration.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(recordDeclaration.isStatic(), "Top level Records are NOT implicitly static.");
    }

    /**
     * https://openjdk.java.net/jeps/395#Restrictions-on-records
     */
    @Test
    void record_nestedRecordsAreImplicitlyStatic() {
        String s = "\n" +
                "class X {\n" +
                "    record Point(int x, int y) {\n" +
                "    }\n" +
                "}\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        RecordDeclaration recordDeclaration = cu.findAll(RecordDeclaration.class).get(0);
        assertFalse(recordDeclaration.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(recordDeclaration.isStatic(), "Nested Records are implicitly static.");

    }


    @Test
    void record_canBeCreatedUsingKeywordNew() {
        String s = "\n" +
                "\n" +
                "record Point(int x, int y) {\n" +
                "}\n" +
                "\n" +
                "class X {\n" +
                "    public static void main(String[] args) {\n" +
                "        new Point(10, 3);\n" +
                "    }\n" +
                "}\n\n";

        CompilationUnit cu = TestParser.parseCompilationUnit(s);
        assertOneRecordDeclaration(cu);

        ClassOrInterfaceDeclaration coid = cu.findAll(ClassOrInterfaceDeclaration.class).get(0);
        List<ObjectCreationExpr> objectCreationExprs = coid.findAll(ObjectCreationExpr.class);

        assertEquals(1, objectCreationExprs.size());
        ObjectCreationExpr objectCreationExpr = objectCreationExprs.get(0);
        assertEquals("Point", objectCreationExpr.getTypeAsString());
    }

    /**
     * Note the Record Declaration Constructor does not include parameters.
     * (parameters are, instead, included within the record declaration)
     * <p>
     * https://bugs.openjdk.java.net/browse/JDK-8222777
     */
    @Test
    void recordDeclarationFromTheJDK8222777() {
        CompilationUnit cu = TestParser.parseCompilationUnit("" +
                "public record Range(int lo, int hi) {\n" +
                "\n" +
                "  public Range {\n" +
                "    if (lo > hi)  /* referring here to the implicit constructor parameters */\n" +
                "      throw new IllegalArgumentException(String.format(\"(%d,%d)\", lo, hi));\n" +
                "  }\n" +
                "}"
        );

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertThat(recordDeclaration.getNameAsString()).isEqualTo("Range");
        assertThat(recordDeclaration.getModifiers()).containsExactly(Modifier.publicModifier());
        // test parameters
        // get constructor
        // test parameters (none)
    }

    @Test
    void recordDeclaration_exampleFromJls_8_10_4_1_normalCanonicalConstructors() {
        CompilationUnit cu = TestParser.parseCompilationUnit("" +
                "import java.lang.annotation.Target;\n" +
                "import java.lang.annotation.ElementType;\n" +
                "\n" +
                "@interface Foo {}\n" +
                "@interface Bar {}\n" +
                "\n" +
                "record Person(@Foo String name) {\n" +
                "    Person(String name2) {\n" +
                "    }\n" +
                "}"
        );

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertThat(recordDeclaration.getNameAsString()).isEqualTo("Person");
        assertThat(recordDeclaration.getModifiers()).isEmpty();

        assertThat(recordDeclaration.getConstructors()).hasSize(1);
        assertThat(recordDeclaration.getCompactConstructors()).hasSize(0);

    }

    @Test
    void compactConstructor_exampleFromJls_8_10_4_2_compactConstructors() {
        CompilationUnit cu = TestParser.parseCompilationUnit("" +
                "record Rational(int num, int denom) {\n" +
                "    private static int gcd(int a, int b) {\n" +
                "        if (b == 0) return Math.abs(a);\n" +
                "        else return gcd(b, a % b);\n" +
                "    }\n" +
                "   \n" +
                "    Rational {\n" +
                "        int gcd = gcd(num, denom);\n" +
                "        num    /= gcd;\n" +
                "        denom  /= gcd;\n" +
                "    }\n" +
                "}\n"
        );

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertThat(recordDeclaration.getNameAsString()).isEqualTo("Rational");
        assertThat(recordDeclaration.getModifiers()).isEmpty();

        assertThat(recordDeclaration.getConstructors()).hasSize(0);
        assertThat(recordDeclaration.getCompactConstructors()).hasSize(1);

    }

    @Test
    void nonCompactConstructor_exampleFromJls_8_10_4_2_compactConstructors() {
        CompilationUnit cu = TestParser.parseCompilationUnit("" +
                "record Rational(int num, int denom) {\n" +
                "    private static int gcd(int a, int b) {\n" +
                "        if (b == 0) return Math.abs(a);\n" +
                "        else return gcd(b, a % b);\n" +
                "    }\n" +
                "   \n" +
                "    Rational(int num, int demon) {\n" +
                "        int gcd = gcd(num, denom);\n" +
                "        num    /= gcd;\n" +
                "        denom  /= gcd;\n" +
                "        this.num   = num;\n" +
                "        this.denom = denom;\n" +
                "    }\n" +
                "}\n"
        );

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertThat(recordDeclaration.getNameAsString()).isEqualTo("Rational");
        assertThat(recordDeclaration.getModifiers()).isEmpty();

        assertThat(recordDeclaration.getConstructors()).hasSize(1);
        assertThat(recordDeclaration.getCompactConstructors()).hasSize(0);

    }

    /**
     * https://openjdk.java.net/jeps/395
     */
    @Test
    void localRecords() {
        CompilationUnit cu = TestParser.parseCompilationUnit("" +
                "class Scratch {\n" +
                "    List<Merchant> findTopMerchants(List<Merchant> merchants, int month) {\n" +
                "        // Local record\n" +
                "        record MerchantSales(Merchant merchant, double sales) {}\n" +
                "\n" +
                "        return merchants.stream()\n" +
                "                .map(merchant -> new MerchantSales(merchant, computeSales(merchant, month)))\n" +
                "                .sorted((m1, m2) -> Double.compare(m2.sales(), m1.sales()))\n" +
                "                .map(MerchantSales::merchant)\n" +
                "                .collect(toList());\n" +
                "    }\n" +
                "}\n"
        );

        RecordDeclaration recordDeclaration = cu.findFirst(RecordDeclaration.class).get();
        assertThat(recordDeclaration.getNameAsString()).isEqualTo("MerchantSales");

    }

    @Test
    void instanceFieldIsNotAllowedInRecord() {
        String s = "record X { int record; }";

        assertThrows(AssertionFailedError.class, () -> {
            CompilationUnit cu = TestParser.parseCompilationUnit(s);
        });
    }

    private void assertCompilationFails(String s) {
        assertThrows(AssertionFailedError.class, () -> {
            CompilationUnit cu = TestParser.parseCompilationUnit(s);
        });
    }

    private void assertOneRecordDeclaration(CompilationUnit cu) {
        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());
    }

    private void assertTwoRecordDeclarations(CompilationUnit cu) {
        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(2, recordDeclarations.size());
    }
}
