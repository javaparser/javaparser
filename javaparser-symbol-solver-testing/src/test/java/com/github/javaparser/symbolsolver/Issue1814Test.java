package com.github.javaparser.symbolsolver;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import java.time.Duration;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * @author Dominik Hardtke
 * @since 01/09/2018
 */
class Issue1814Test extends AbstractResolutionTest {
    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        final CompilationUnit compilationUnit = new CompilationUnit();
        compilationUnit.setPackageDeclaration("java.lang");
        // construct a fake java.lang.Object class with only one method (java.lang.Object#equals(java.lang.Object)
        final ClassOrInterfaceDeclaration clazz = compilationUnit.addClass("Object", Modifier.Keyword.PUBLIC);
        final MethodDeclaration equals = clazz.addMethod("equals", Modifier.Keyword.PUBLIC);
        equals.addParameter("Object", "obj");
        final BlockStmt body = new BlockStmt();
        body.addStatement("return this == obj;");
        equals.setBody(body);

        TypeSolver typeSolver = new TypeSolver() {
            @Override
            public TypeSolver getParent() {
                return null;
            }

            @Override
            public void setParent(TypeSolver parent) {
            }

            @Override
            public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
                if ("java.lang.Object".equals(name)) {
                    // custom handling
                    return SymbolReference.solved(new JavaParserClassDeclaration(clazz, this));
                }

                return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
            }
        };

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        javaParser = new JavaParser(config);
    }

    @Test
    void getAllMethodsVisibleToInheritors() {
        assertTimeoutPreemptively(Duration.ofMillis(1000L), () -> {
            String code = String.join(System.lineSeparator(), "public class AbstractExercise extends java.lang.Object {", "}");
            ParseResult<CompilationUnit> parseResult = javaParser.parse(ParseStart.COMPILATION_UNIT, Providers.provider(code));
            assertTrue(parseResult.isSuccessful());
            assertTrue(parseResult.getResult().isPresent());
            List<ClassOrInterfaceType> referenceTypes = parseResult.getResult().get().findAll(ClassOrInterfaceType.class);
            assertTrue(referenceTypes.size() > 0);
            final List<ResolvedMethodDeclaration> methods = referenceTypes.get(0).resolve().getAllMethodsVisibleToInheritors();
            assertEquals(1, methods.size());
        });


    }
}
