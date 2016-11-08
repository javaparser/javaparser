package com.github.javaparser.ast.imports;

import com.github.javaparser.ast.expr.Name;
import org.junit.Test;

import static com.github.javaparser.Range.UNKNOWN;
import static org.junit.Assert.assertEquals;

public class ImportDeclarationTest {
    @Test
    public void singleTypeImportDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, Name.parse("a.b.c.X"), false, false);
        SingleTypeImportDeclaration i = (SingleTypeImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().getNameAsString());
    }

    @Test
    public void typeImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, Name.parse("a.b.c.D"), false, true);
        TypeImportOnDemandDeclaration i = (TypeImportOnDemandDeclaration) importDeclaration;
        assertEquals("a.b.c.D", i.getNameAsString());
        assertEquals("D", i.getName().getId());
    }

    @Test
    public void singleStaticImportDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, Name.parse("a.b.c.X.def"), true, false);
        SingleStaticImportDeclaration i = (SingleStaticImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().getNameAsString());
        assertEquals("def", i.getStaticMember());
    }

    @Test
    public void staticImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = ImportDeclaration.create(UNKNOWN, Name.parse("a.b.c.X"), true, true);
        StaticImportOnDemandDeclaration i = (StaticImportOnDemandDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().getNameAsString());
    }

}