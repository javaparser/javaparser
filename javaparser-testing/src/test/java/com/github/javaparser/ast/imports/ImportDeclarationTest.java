package com.github.javaparser.ast.imports;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import com.github.javaparser.ast.expr.Name;

public class ImportDeclarationTest {
    @Test
    public void singleTypeImportDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(null, Name.parse("a.b.c.X"), false, false);
        SingleTypeImportDeclaration i = (SingleTypeImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().toString());
    }

    @Test
    public void typeImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(null, Name.parse("a.b.c.D"), false, true);
        TypeImportOnDemandDeclaration i = (TypeImportOnDemandDeclaration) importDeclaration;
        assertEquals("a.b.c.D", i.getName().toString());
        assertEquals("D", i.getName().getId());
    }

    @Test
    public void singleStaticImportDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(null, Name.parse("a.b.c.X.def"), true, false);
        SingleStaticImportDeclaration i = (SingleStaticImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().toString());
        assertEquals("def", i.getStaticMember());
    }

    @Test
    public void staticImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(null, Name.parse("a.b.c.X"), true, true);
        StaticImportOnDemandDeclaration i = (StaticImportOnDemandDeclaration) importDeclaration;
        assertEquals("X", i.getType().getNameAsString());
		assertEquals("c", i.getType().getScope().get().getNameAsString());
		assertEquals("b", i.getType().getScope().get().getScope().get().getNameAsString());
		assertEquals("a", i.getType().getScope().get().getScope().get().getScope().get().getNameAsString());
    }

}