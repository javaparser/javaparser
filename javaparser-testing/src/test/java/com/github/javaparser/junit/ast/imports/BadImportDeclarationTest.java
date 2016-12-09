package com.github.javaparser.junit.ast.imports;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ast.imports.BadImportDeclaration;
import com.github.javaparser.ast.imports.ImportDeclaration;
import org.junit.Test;

import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class BadImportDeclarationTest {
    private final JavaParser parser = new JavaParser();

    @Test
    public void whenParsingABadImportThenItIsStoredAsABadImport() {
        ParseResult<ImportDeclaration> parseResult = parser.parse(ParseStart.IMPORT_DECLARATION, provider("import static x;"));

        assertEquals("import static has only one identifier (line 1,col 16)-(line 1,col 16)", parseResult.getProblem(0).toString());
        assertEquals(true, parseResult.getResult().get() instanceof BadImportDeclaration);
    }

    @Test
    public void whenPrintingABadImportThenItIsPrintedLiterally() {
        ParseResult<ImportDeclaration> parseResult = parser.parse(ParseStart.IMPORT_DECLARATION, provider("import    static    x  ;"));

        assertEquals("???" + EOL, parseResult.getResult().get().toString());
    }

}