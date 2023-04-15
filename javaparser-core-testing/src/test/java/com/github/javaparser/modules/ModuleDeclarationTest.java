/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
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
                "@Foo(1)" + SYSTEM_EOL +
                        "@Foo(2)" + SYSTEM_EOL +
                        "@Bar" + SYSTEM_EOL +
                        "module M.N {" + SYSTEM_EOL +
                        "    requires A.B;" + SYSTEM_EOL +
                        "    requires transitive C.D;" + SYSTEM_EOL +
                        "    requires static E.F;" + SYSTEM_EOL +
                        "    requires static transitive G.H;" + SYSTEM_EOL +
                        "    exports P.Q;" + SYSTEM_EOL +
                        "    exports R.S to T1.U1, T2.U2;" + SYSTEM_EOL +
                        "    opens P.Q;" + SYSTEM_EOL +
                        "    opens R.S to T1.U1, T2.U2;" + SYSTEM_EOL +
                        "    uses V.W;" + SYSTEM_EOL +
                        "    provides X.Y with Z1.Z2, Z3.Z4;" + SYSTEM_EOL +
                        "}" + SYSTEM_EOL, cu.toString());

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
                "@Foo(1)" + SYSTEM_EOL +
                        "@Foo(2)" + SYSTEM_EOL +
                        "@Bar" + SYSTEM_EOL +
                        "open module M.N {" + SYSTEM_EOL +
                        "    requires A.B;" + SYSTEM_EOL +
                        "    requires transitive C.D;" + SYSTEM_EOL +
                        "    requires static E.F;" + SYSTEM_EOL +
                        "    requires transitive static G.H;" + SYSTEM_EOL +
                        "    exports P.Q;" + SYSTEM_EOL +
                        "    exports R.S to T1.U1, T2.U2;" + SYSTEM_EOL +
                        "    opens P.Q;" + SYSTEM_EOL +
                        "    opens R.S to T1.U1, T2.U2;" + SYSTEM_EOL +
                        "    uses V.W;" + SYSTEM_EOL +
                        "    provides X.Y with Z1.Z2, Z3.Z4;" + SYSTEM_EOL +
                        "}" + SYSTEM_EOL, ConcreteSyntaxModel.genericPrettyPrint(cu));

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

        assertEqualsStringIgnoringEol("@SuppressWarnings(\"module\")\n" +
                "module com.laamella.base {\n" +
                "    requires transitive java.desktop;\n" +
                "    exports com.laamella.base.entity.channel;\n" +
                "    exports com.laamella.base.entity.channel.internal to com.laamella.core;\n" +
                "    uses com.laamella.base.util.internal.FactoryDelegate;\n" +
                "    exports foo.bar to other.foo, other.bar;\n" +
                "    exports foo.bar.x to other.foo, other.bar;\n" +
                "}\n", moduleDeclaration.toString());
    }
    
    @Test
    void testModifierRequire() {
        ModuleDeclaration moduleDeclaration = new CompilationUnit()
                .setModule("com.laamella.base")
                .addDirective("requires transitive java.desktop;");
        ModuleRequiresDirective moduleRequiresStmt = moduleDeclaration.getDirectives().get(0).asModuleRequiresStmt();
        assertTrue(moduleRequiresStmt.isTransitive());
    }
    
    @Test
    void testModifierStatic() {
        ModuleDeclaration moduleDeclaration = new CompilationUnit()
                .setModule("com.laamella.base")
                .addDirective("requires static java.desktop;");
        ModuleRequiresDirective moduleRequiresStmt = moduleDeclaration.getDirectives().get(0).asModuleRequiresStmt();
        assertTrue(moduleRequiresStmt.isStatic());
    }
}
