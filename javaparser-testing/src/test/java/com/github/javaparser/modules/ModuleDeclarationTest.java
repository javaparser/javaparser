package com.github.javaparser.modules;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.JavaParser.parseName;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

public class ModuleDeclarationTest {
    @Test
    public void moduleInfoKeywordsAreSeenAsIdentifiers() {
        parse("class module { }");
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

        ModuleRequiresStmt moduleRequiresStmt = (ModuleRequiresStmt) module.getModuleStmts().get(0);
        assertThat(moduleRequiresStmt.getNameAsString()).isEqualTo("A.B");
        assertThat(moduleRequiresStmt.getModifiers()).isEmpty();

        ModuleExportsStmt moduleExportsStmt = (ModuleExportsStmt) module.getModuleStmts().get(5);
        assertThat(moduleExportsStmt.getNameAsString()).isEqualTo("R.S");
        assertThat(moduleExportsStmt.getModuleNames()).containsExactly(parseName("T1.U1"), parseName("T2.U2"));

        ModuleOpensStmt moduleOpensStmt = (ModuleOpensStmt) module.getModuleStmts().get(7);
        assertThat(moduleOpensStmt.getNameAsString()).isEqualTo("R.S");
        assertThat(moduleOpensStmt.getModuleNames()).containsExactly(parseName("T1.U1"), parseName("T2.U2"));

        ModuleUsesStmt moduleUsesStmt = (ModuleUsesStmt) module.getModuleStmts().get(8);
        assertThat(moduleUsesStmt.getType().toString()).isEqualTo("V.W");

        ModuleProvidesStmt moduleProvidesStmt = (ModuleProvidesStmt) module.getModuleStmts().get(9);
        assertThat(moduleProvidesStmt.getType().toString()).isEqualTo("X.Y");
        assertThat(moduleProvidesStmt.getWithTypes()).containsExactly(
                new ClassOrInterfaceType(new ClassOrInterfaceType("Z1"), "Z2"),
                new ClassOrInterfaceType(new ClassOrInterfaceType("Z3"), "Z4"));

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
