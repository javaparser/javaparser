package com.github.javaparser.symbolsolver.resolution.javaparser;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_10;
import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class VarTypeTest {
    private final TypeSolver typeSolver = new ReflectionTypeSolver();
    private final JavaParser javaParser = new JavaParser(new ParserConfiguration()
            .setLanguageLevel(JAVA_10)
            .setSymbolResolver(new JavaSymbolSolver(typeSolver)));

    @Test
    void resolveAPrimitive() {
        CompilationUnit ast = javaParser.parse(ParseStart.COMPILATION_UNIT, provider("class X{void x(){var abc = 1;}}")).getResult().get();
        VarType varType = ast.findFirst(VarType.class).get();

        ResolvedType resolvedType = varType.resolve();

        assertEquals(ResolvedPrimitiveType.INT, resolvedType);
    }

    @Test
    void resolveAReferenceType() {
        CompilationUnit ast = javaParser.parse(ParseStart.COMPILATION_UNIT, provider("class X{void x(){var abc = \"\";}}")).getResult().get();
        VarType varType = ast.findFirst(VarType.class).get();

        ResolvedType resolvedType = varType.resolve();

        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver), resolvedType);
    }

    @Test
    void failResolveNoInitializer() {
        assertThrows(IllegalStateException.class, () -> {
            CompilationUnit ast = javaParser.parse(ParseStart.COMPILATION_UNIT, provider("class X{void x(){var abc;}}")).getResult().get();
        VarType varType = ast.findFirst(VarType.class).get();
        varType.resolve();
    });
        
}

    @Test
    void failResolveWrongLocation() {
        assertThrows(IllegalStateException.class, () -> {
            CompilationUnit ast = javaParser.parse(ParseStart.COMPILATION_UNIT, provider("class X{void x(var x){};}")).getResult().get();
        VarType varType = ast.findFirst(VarType.class).get();
        varType.resolve();
    });
        
}
}
