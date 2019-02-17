package com.github.javaparser.modules;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.GeneratedJavaParserConstants.IDENTIFIER;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_9;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.StaticJavaParser.parseName;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.*;

class ModuleDeclarationTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_9));

    private CompilationUnit parse(String code) {
        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider(code));
        if(!result.isSuccessful()){
            System.err.println(result);
        }
        return result.getResult().get();
    }

    @Test
    void moduleInfoKeywordsAreSeenAsIdentifiers() {
        CompilationUnit cu = parse("class module { }");
        JavaToken moduleToken = cu.getClassByName("module").get().getName().getTokenRange().get().getBegin();
        assertEquals(IDENTIFIER, moduleToken.getKind());
    }

    @Test
    void issue988RequireTransitiveShouldRequireAModuleCalledTransitive() {
        CompilationUnit cu = parse("module X { requires transitive; }");
        ModuleRequiresDirective requiresTransitive = (ModuleRequiresDirective) cu.getModule().get().getDirectives().get(0);
        assertEquals("transitive", requiresTransitive.getNameAsString());
        assertEquals(IDENTIFIER, requiresTransitive.getName().getTokenRange().get().getBegin().getKind());
    }

    @Test
    void jlsExample1() {
        CompilationUnit cu = parse(
                "@Foo(1) @Foo(2) @Bar " +
                        "module M.N {" +
                        "  requires A.B;" +
                        "  requires transitive C.D;" +
                        "  requires static E.F;" +
                        "  requires transitive static G.H;" +
                        "" +
                        "  exports P.Q;" +
                        "  exports R.S to T1.U1, T2.U2;" +
                        "" +
                        "  opens P.Q;" +
                        "  opens R.S to T1.U1, T2.U2;" +
                        "" +
                        "  uses V.W;" +
                        "  provides X.Y with Z1.Z2, Z3.Z4;" +
                        "}");

        ModuleDeclaration module = cu.getModule().get();
        assertEquals("M.N", module.getNameAsString());
        assertFalse(module.isOpen());
        assertThat(module.getAnnotations()).containsExactly(
                new SingleMemberAnnotationExpr(new Name("Foo"), new IntegerLiteralExpr("1")),
                new SingleMemberAnnotationExpr(new Name("Foo"), new IntegerLiteralExpr("2")),
                new MarkerAnnotationExpr(new Name("Bar")));

        ModuleRequiresDirective moduleRequiresStmt = module.getDirectives().get(0).asModuleRequiresStmt();
        assertThat(moduleRequiresStmt.getNameAsString()).isEqualTo("A.B");
        assertThat(moduleRequiresStmt.getModifiers()).isEmpty();

        ModuleExportsDirective moduleExportsStmt = module.getDirectives().get(5).asModuleExportsStmt();
        assertThat(moduleExportsStmt.getNameAsString()).isEqualTo("R.S");
        assertThat(moduleExportsStmt.getModuleNames()).containsExactly(parseName("T1.U1"), parseName("T2.U2"));

        ModuleOpensDirective moduleOpensStmt = module.getDirectives().get(7).asModuleOpensStmt();
        assertThat(moduleOpensStmt.getNameAsString()).isEqualTo("R.S");
        assertThat(moduleOpensStmt.getModuleNames()).containsExactly(parseName("T1.U1"), parseName("T2.U2"));

        ModuleUsesDirective moduleUsesStmt = module.getDirectives().get(8).asModuleUsesStmt();
        assertThat(moduleUsesStmt.getNameAsString()).isEqualTo("V.W");

        ModuleProvidesDirective moduleProvidesStmt = module.getDirectives().get(9).asModuleProvidesStmt();
        assertThat(moduleProvidesStmt.getNameAsString()).isEqualTo("X.Y");
        assertThat(moduleProvidesStmt.getWith()).containsExactly(
                parseName("Z1.Z2"),
                parseName("Z3.Z4"));

    }

    @Test
    void jlsExample2HasAnOpenModule() {
        CompilationUnit cu = parse("open module M.N {}");

        ModuleDeclaration module = cu.getModule().get();
        assertEquals("M.N", module.getNameAsString());
        assertTrue(module.isOpen());
    }

    @Test
    void testPrettyPrinting() {
        CompilationUnit cu = parse(
                "@Foo(1) @Foo(2) @Bar " +
                        "module M.N {" +
                        "  requires A.B;" +
                        "  requires transitive C.D;" +
                        "  requires static E.F;" +
                        "  requires static transitive G.H;" +
                        "" +
                        "  exports P.Q;" +
                        "  exports R.S to T1.U1, T2.U2;" +
                        "" +
                        "  opens P.Q;" +
                        "  opens R.S to T1.U1, T2.U2;" +
                        "" +
                        "  uses V.W;" +
                        "  provides X.Y with Z1.Z2, Z3.Z4;" +
                        "}");

        assertEquals(
                "@Foo(1)" + EOL +
                        "@Foo(2)" + EOL +
                        "@Bar" + EOL +
                        "module M.N {" + EOL +
                        "    requires A.B;" + EOL +
                        "    requires transitive C.D;" + EOL +
                        "    requires static E.F;" + EOL +
                        "    requires static transitive G.H;" + EOL +
                        "    exports P.Q;" + EOL +
                        "    exports R.S to T1.U1, T2.U2;" + EOL +
                        "    opens P.Q;" + EOL +
                        "    opens R.S to T1.U1, T2.U2;" + EOL +
                        "    uses V.W;" + EOL +
                        "    provides X.Y with Z1.Z2, Z3.Z4;" + EOL +
                        "}" + EOL, cu.toString());

    }

    @Test
    void testCsmPrinting() {
        CompilationUnit cu = parse(
                "@Foo(1) @Foo(2) @Bar " +
                        "open module M.N {" +
                        "  requires A.B;" +
                        "  requires transitive C.D;" +
                        "  requires static E.F;" +
                        "  requires transitive static G.H;" +
                        "" +
                        "  exports P.Q;" +
                        "  exports R.S to T1.U1, T2.U2;" +
                        "" +
                        "  opens P.Q;" +
                        "  opens R.S to T1.U1, T2.U2;" +
                        "" +
                        "  uses V.W;" +
                        "  provides X.Y with Z1.Z2, Z3.Z4;" +
                        "}");

        assertEquals(
                "@Foo(1)" + EOL +
                        "@Foo(2)" + EOL +
                        "@Bar" + EOL +
                        "open module M.N {" + EOL +
                        "    requires A.B;" + EOL +
                        "    requires transitive C.D;" + EOL +
                        "    requires static E.F;" + EOL +
                        "    requires transitive static G.H;" + EOL +
                        "    exports P.Q;" + EOL +
                        "    exports R.S to T1.U1, T2.U2;" + EOL +
                        "    opens P.Q;" + EOL +
                        "    opens R.S to T1.U1, T2.U2;" + EOL +
                        "    uses V.W;" + EOL +
                        "    provides X.Y with Z1.Z2, Z3.Z4;" + EOL +
                        "}" + EOL, ConcreteSyntaxModel.genericPrettyPrint(cu));

    }

    @Test
    void fluentInterface() {
        ModuleDeclaration moduleDeclaration = new CompilationUnit()
                .setModule("com.laamella.base")
                .addSingleMemberAnnotation(SuppressWarnings.class, "\"module\"")
                .addDirective("requires transitive java.desktop;")
                .addDirective("exports com.laamella.base.entity.channel;")
                .addDirective("exports com.laamella.base.entity.channel.internal to com.laamella.core;")
                .addDirective("uses com.laamella.base.util.internal.FactoryDelegate;");

        moduleDeclaration.getDirectives()
                .addLast(new ModuleExportsDirective()
                        .setName("foo.bar")
                        .addModuleName("other.foo")
                        .addModuleName("other.bar")
                );

        moduleDeclaration
                .addDirective(new ModuleExportsDirective()
                        .setName("foo.bar.x")
                        .addModuleName("other.foo")
                        .addModuleName("other.bar")
                );

        assertEqualsNoEol("@SuppressWarnings(\"module\")\n" +
                "module com.laamella.base {\n" +
                "    requires transitive java.desktop;\n" +
                "    exports com.laamella.base.entity.channel;\n" +
                "    exports com.laamella.base.entity.channel.internal to com.laamella.core;\n" +
                "    uses com.laamella.base.util.internal.FactoryDelegate;\n" +
                "    exports foo.bar to other.foo, other.bar;\n" +
                "    exports foo.bar.x to other.foo, other.bar;\n" +
                "}\n", moduleDeclaration.toString());
    }
}
