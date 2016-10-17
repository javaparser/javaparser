package com.github.javaparser.ast.imports;

import com.github.javaparser.ast.expr.NameExpr;
import org.junit.Test;

import static com.github.javaparser.Range.UNKNOWN;
import static org.junit.Assert.assertEquals;

public class ImportDeclarationTest {
    @Test
    public void singleTypeImportDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, NameExpr.name("a.b.c.X"), false, false);
        SingleTypeImportDeclaration i = (SingleTypeImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().getName());
    }

    @Test
    public void typeImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, NameExpr.name("a.b.c.D"), false, true);
        TypeImportOnDemandDeclaration i = (TypeImportOnDemandDeclaration) importDeclaration;
        assertEquals("a.b.c.D", i.getName().getQualifiedName());
        assertEquals("D", i.getName().getName());
    }

    @Test
    public void singleStaticImportDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, NameExpr.name("a.b.c.X.def"), true, false);
        SingleStaticImportDeclaration i = (SingleStaticImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().getName());
        assertEquals("def", i.getStaticMember());
    }

    @Test
    public void staticImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, NameExpr.name("a.b.c.X"), true, true);
        StaticImportOnDemandDeclaration i = (StaticImportOnDemandDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().getName());
    }

}