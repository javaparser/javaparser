package com.github.javaparser.symbolsolver.resolution.javaparser;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.jupiter.api.Assertions.assertEquals;

class SwitchExprTest {
    private final TypeSolver typeSolver = new ReflectionTypeSolver();
    private final JavaParser javaParser = new JavaParser(new ParserConfiguration()
            .setLanguageLevel(BLEEDING_EDGE)
            .setSymbolResolver(new JavaSymbolSolver(typeSolver)));

    @Test
    void switchEntryHasIntExpression() {
        CompilationUnit ast = javaParser.parse("class X{void x(){Object a=switch(a){case 1 -> 3+4;};}}").getResult().get();
        ResolvedType resolvedType = ast.findFirst(SwitchExpr.class).get().calculateResolvedType();
        assertEquals(ResolvedPrimitiveType.INT, resolvedType);
    }

    @Test
    void switchEntryBreaksWithIntAndString() {
        CompilationUnit ast = javaParser.parse("class X{void x(){Object a=switch(a){case 1-> {if(x){break 3+4;}else{break \"oops\";}}};}}").getResult().get();
        ResolvedType resolvedType = ast.findFirst(SwitchExpr.class).get().calculateResolvedType();
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver), resolvedType);
    }

    @Test
    void switchEntryBreaksInsideStatementBlock() {
        CompilationUnit ast = javaParser.parse("class X{void x(){Object a=switch(a){case 1-> {a(); b(); break 3+4;}}; }}").getResult().get();
        ResolvedType resolvedType = ast.findFirst(SwitchExpr.class).get().calculateResolvedType();
        assertEquals(ResolvedPrimitiveType.INT, resolvedType);
    }

    @Test
    void multipleSwitchEntriesReturnDifferentTypes() {
        CompilationUnit ast = javaParser.parse("class X{void x(){Object a=switch(a){case 1-> 1; case 2->\"\"; default->1.0; };}}").getResult().get();
        ResolvedType resolvedType = ast.findFirst(SwitchExpr.class).get().calculateResolvedType();
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver), resolvedType);
    }

}
