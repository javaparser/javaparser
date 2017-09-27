package com.github.javaparser.modules;

import com.github.javaparser.JavaParser;
import com.github.javaparser.JavaToken;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.validator.Java9Validator;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import org.junit.Test;

import static com.github.javaparser.GeneratedJavaParserConstants.IDENTIFIER;
import static com.github.javaparser.JavaParser.parseClassOrInterfaceType;
import static com.github.javaparser.JavaParser.parseName;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

public class ModuleDeclarationTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));

    private final CompilationUnit parse(String code) {
        return javaParser.parse(ParseStart.COMPILATION_UNIT, provider(code)).getResult().get();
    }

    @Test
    public void moduleInfoKeywordsAreSeenAsIdentifiers() {
        CompilationUnit cu = parse("class module { }");
        JavaToken moduleToken = cu.getClassByName("module").get().getName().getTokenRange().get().getBegin();
        assertEquals(IDENTIFIER, moduleToken.getKind());
    }

    @Test
    public void issue988RequireTransitiveShouldRequireAModuleCalledTransitive() {
        CompilationUnit cu = parse("module X { requires transitive; }");
        ModuleRequiresStmt requiresTransitive = (ModuleRequiresStmt) cu.getModule().get().getModuleStmts().get(0);
        assertEquals("transitive", requiresTransitive.getNameAsString());
        assertEquals(IDENTIFIER, requiresTransitive.getName().getTokenRange().get().getBegin().getKind());
    }

    @Test
    public void jlsExample1() {
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
        assertEquals(false, module.isOpen());
        assertThat(module.getAnnotations()).containsExactly(
                new SingleMemberAnnotationExpr(new Name("Foo"), new IntegerLiteralExpr("1")),
                new SingleMemberAnnotationExpr(new Name("Foo"), new IntegerLiteralExpr("2")),
                new MarkerAnnotationExpr(new Name("Bar")));

        ModuleRequiresStmt moduleRequiresStmt = module.getModuleStmts().get(0).asModuleRequiresStmt();
        assertThat(moduleRequiresStmt.getNameAsString()).isEqualTo("A.B");
        assertThat(moduleRequiresStmt.getModifiers()).isEmpty();

        ModuleExportsStmt moduleExportsStmt = module.getModuleStmts().get(5).asModuleExportsStmt();
        assertThat(moduleExportsStmt.getNameAsString()).isEqualTo("R.S");
        assertThat(moduleExportsStmt.getModuleNames()).containsExactly(parseName("T1.U1"), parseName("T2.U2"));

        ModuleOpensStmt moduleOpensStmt = module.getModuleStmts().get(7).asModuleOpensStmt();
        assertThat(moduleOpensStmt.getNameAsString()).isEqualTo("R.S");
        assertThat(moduleOpensStmt.getModuleNames()).containsExactly(parseName("T1.U1"), parseName("T2.U2"));

        ModuleUsesStmt moduleUsesStmt = module.getModuleStmts().get(8).asModuleUsesStmt();
        assertThat(moduleUsesStmt.getType().toString()).isEqualTo("V.W");

        ModuleProvidesStmt moduleProvidesStmt = module.getModuleStmts().get(9).asModuleProvidesStmt();
        assertThat(moduleProvidesStmt.getType().toString()).isEqualTo("X.Y");
        assertThat(moduleProvidesStmt.getWithTypes()).containsExactly(
                new ClassOrInterfaceType(parseClassOrInterfaceType("Z1"), "Z2"),
                new ClassOrInterfaceType(parseClassOrInterfaceType("Z3"), "Z4"));

    }

    @Test
    public void jlsExample2HasAnOpenModule() {
        CompilationUnit cu = parse("open module M.N {}");

        ModuleDeclaration module = cu.getModule().get();
        assertEquals("M.N", module.getNameAsString());
        assertEquals(true, module.isOpen());
    }

    @Test
    public void testPrettyPrinting() {
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

        assertEquals(
                "@Foo(1) @Foo(2) @Bar " + EOL +
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
    public void testCsmPrinting() {
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
                "@Foo(1) @Foo(2) @Bar" + EOL +
                        "open module M.N {" + EOL +
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
                        "}" + EOL, ConcreteSyntaxModel.genericPrettyPrint(cu));

    }
}
