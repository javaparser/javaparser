package com.github.javaparser.ast.imports;

import com.github.javaparser.JavaParser;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ImportDeclarationTest {
    @Test
    public void singleTypeImportDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import a.b.c.X;");
        SingleTypeImportDeclaration i = (SingleTypeImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().toString());
    }

    @Test
    public void typeImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import a.b.c.D.*;");
        TypeImportOnDemandDeclaration i = (TypeImportOnDemandDeclaration) importDeclaration;
        assertEquals("a.b.c.D", i.getName().toString());
        assertEquals("D", i.getName().getIdentifier());
    }

    @Test
    public void singleStaticImportDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import static a.b.c.X.def;");
        SingleStaticImportDeclaration i = (SingleStaticImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().toString());
        assertEquals("def", i.getStaticMember());
    }

    @Test
    public void staticImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import static a.b.c.X.*;");
        StaticImportOnDemandDeclaration i = (StaticImportOnDemandDeclaration) importDeclaration;
        assertEquals("X", i.getType().getNameAsString());
        assertEquals("c", i.getType().getScope().get().getNameAsString());
        assertEquals("b", i.getType().getScope().get().getScope().get().getNameAsString());
        assertEquals("a", i.getType().getScope().get().getScope().get().getScope().get().getNameAsString());
    }

}