package me.tomassetti.symbolsolver.model;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.Type;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesolvers.DummyTypeSolver;
import me.tomassetti.symbolsolver.model.typesolvers.JarTypeSolver;
import me.tomassetti.symbolsolver.model.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.Optional;

import static org.easymock.EasyMock.*;
import static org.junit.Assert.assertEquals;

public class GenericsTest {

    private CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = GenericsTest.class.getClassLoader().getResourceAsStream(sampleName + ".java.txt");
        return JavaParser.parse(is);
    }

    @Test
    public void resolveFieldWithGenericTypeToString() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "s");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("s", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("s", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(1, typeUsage.parameters().size());
        assertEquals("java.lang.String", typeUsage.parameters().get(0).getTypeName());
    }

    @Test
    public void resolveFieldWithGenericTypeToDeclaredClass() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "g");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("g", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("g", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(1, typeUsage.parameters().size());
        assertEquals("me.tomassetti.symbolsolver.javaparser.Generics", typeUsage.parameters().get(0).getTypeName());
    }

    @Test
    public void resolveFieldWithGenericTypeToInteger() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "i");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("i", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("i", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(1, typeUsage.parameters().size());
        assertEquals("java.lang.Integer", typeUsage.parameters().get(0).getTypeName());
    }

}
