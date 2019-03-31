package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class Issue347Test extends AbstractResolutionTest{

    private TypeSolver typeSolver;
    private JavaParserFacade javaParserFacade;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
        javaParserFacade = JavaParserFacade.get(typeSolver);
    }

    @Test
    void resolvingReferenceToEnumDeclarationInSameFile() {
        String code = "package foo.bar;\nenum Foo {\n" +
                "    FOO_A, FOO_B\n" +
                "}\n" +
                "\n" +
                "class UsingFoo {\n" +
                "    Foo myFooField;\n" +
                "}";
        CompilationUnit cu = parse(code);
        FieldDeclaration fieldDeclaration = Navigator.findNodeOfGivenClass(cu, FieldDeclaration.class);
        ResolvedType fieldType = javaParserFacade.getType(fieldDeclaration);
        assertTrue(fieldType.isReferenceType());
        assertTrue(fieldType.asReferenceType().getTypeDeclaration().isEnum());
        assertEquals("foo.bar.Foo", fieldType.asReferenceType().getQualifiedName());
    }
}

