package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.reflection.*;
import me.tomassetti.symbolsolver.model.typesolvers.DummyTypeSolver;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import org.junit.Test;
import static org.junit.Assert.*;

import java.io.InputStream;
import java.util.Optional;

/**
 * Created by federico on 18/08/15.
 */
public class ClassOrInterfaceDeclarationContextTest {

    private CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = this.getClass().getClassLoader().getResourceAsStream(sampleName + ".java.txt");
        return JavaParser.parse(is);
    }

    @Test
    public void solveExistingGenericType() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<TypeUsage> a = context.solveGenericType("A", new DummyTypeSolver());
        Optional<TypeUsage> b = context.solveGenericType("B", new DummyTypeSolver());
        Optional<TypeUsage> c = context.solveGenericType("C", new DummyTypeSolver());

        assertEquals(true, a.isPresent());
        assertEquals("A", a.get().getTypeName());
        assertEquals(true, a.get().isTypeVariable());
        assertEquals(true, b.isPresent());
        assertEquals("B", b.get().getTypeName());
        assertEquals(true, b.get().isTypeVariable());
        assertEquals(true, c.isPresent());
        assertEquals("C", c.get().getTypeName());
        assertEquals(true, c.get().isTypeVariable());
    }

    @Test
    public void solveUnexistingGenericType() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<TypeUsage> d = context.solveGenericType("D", new DummyTypeSolver());

        assertEquals(false, d.isPresent());
    }

}
