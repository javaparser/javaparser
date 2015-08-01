package me.tomassetti.symbolsolver.model.typesolvers;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import javassist.ClassPool;
import javassist.CtClass;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import org.junit.Test;
import static org.easymock.EasyMock.*;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.net.URLDecoder;
import java.util.Collection;
import java.util.Collections;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarInputStream;

import static org.junit.Assert.*;


public class JarTypeSolverTest {

    @Test
    public void initial() throws IOException {
        String pathToJar = "src/test/resources/javaparser-core-2.1.0.jar";
        JarTypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.SourcesHelper").isSolved());
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.Token").isSolved());
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.ASTParser.JJCalls").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("com.github.javaparser.ASTParser.Foo").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("com.github.javaparser.Foo").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("Foo").isSolved());
    }

}
