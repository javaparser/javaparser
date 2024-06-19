package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;

public class JavaParserRecordDeclarationTest {

    private final String basicRecord = "record Test() {}";
    private final String basicRecordWithPackage = "package x.y; record Test() {}";
    private final String basicRecordWithImplements = "" + "interface A {}\n" + "record Test() implements A {}";

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        // clear internal caches
        JavaParserFacade.clearInstances();

        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()))
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16);
        javaParser = new JavaParser(configuration);
    }

    @Test
    void testIsRecord() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertTrue(resolvedReferenceTypeDeclaration.isRecord());
    }

    @Test
    void testIsClass() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isClass());
    }

    @Test
    void testIsInterface() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isInterface());
    }

    @Test
    void testIsEnum() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isTypeParameter());
    }

    @Test
    void testIsType() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertTrue(resolvedReferenceTypeDeclaration.isType());
    }

    @Test
    void testAsType() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals(resolvedReferenceTypeDeclaration, resolvedReferenceTypeDeclaration.asType());
    }

    @Test
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
            CompilationUnit compilationUnit = x.getResult().get();

            RecordDeclaration recordDeclaration =
                    compilationUnit.findFirst(RecordDeclaration.class).get();
            ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

            assertEquals(resolvedReferenceTypeDeclaration, resolvedReferenceTypeDeclaration.asClass());
        });
    }

    @Test
    void testAsRecord() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals(resolvedReferenceTypeDeclaration, resolvedReferenceTypeDeclaration.asRecord());
    }

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
            CompilationUnit compilationUnit = x.getResult().get();

            RecordDeclaration recordDeclaration =
                    compilationUnit.findFirst(RecordDeclaration.class).get();
            ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

            resolvedReferenceTypeDeclaration.asInterface();
        });
    }

    @Test
    void testAsEnum() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
            CompilationUnit compilationUnit = x.getResult().get();

            RecordDeclaration recordDeclaration =
                    compilationUnit.findFirst(RecordDeclaration.class).get();
            ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

            resolvedReferenceTypeDeclaration.asEnum();
        });
    }

    @Test
    void testGetPackageName() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals("x.y", resolvedReferenceTypeDeclaration.getPackageName());
    }

    @Test
    void testGetClassName() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals("Test", resolvedReferenceTypeDeclaration.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals("x.y.Test", resolvedReferenceTypeDeclaration.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

    @Test
    @EnabledForJreRange(max = org.junit.jupiter.api.condition.JRE.JAVA_13)
    void getGetAncestors_javaLangRecord_notAvailable() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithImplements);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        /*
         * `java.lang.Record` will have been introduced from  JRE14 preview / JRE16 release
         *  -- thus the `java.lang.Record` ancestor will not be available via classloader/reflection before these versions
         */
        assertThrows(UnsolvedSymbolException.class, () -> resolvedReferenceTypeDeclaration.getAncestors());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void getGetAncestors_javaLangRecord_available() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithImplements);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        List<ResolvedReferenceType> ancestors = resolvedReferenceTypeDeclaration.getAncestors();
        assertEquals(2, ancestors.size());
        assertEquals("java.lang.Record", ancestors.get(0).getQualifiedName());
        assertEquals("A", ancestors.get(1).getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testReflectionGetDeclaredFields() {
        ParseResult<CompilationUnit> x = javaParser.parse("record Test(String s, Integer i) {}");
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        List<ResolvedFieldDeclaration> fields = resolvedRecordDeclaration.getAllFields();
        assertEquals(2, fields.size());
        assertEquals("java.lang.String", fields.get(0).getType().describe());
        assertEquals("s", fields.get(0).getName());
        assertEquals("java.lang.Integer", fields.get(1).getType().describe());
        assertEquals("i", fields.get(1).getName());
    }
}
