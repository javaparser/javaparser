package me.tomassetti.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.google.common.collect.ImmutableSet;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.model.declarations.Declaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.AbstractTest;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.stream.Collectors;

import static org.junit.Assert.*;

public class FindingAllFields extends AbstractTest {

    @Test
    public void findAllInheritedFields() throws ParseException {
        CompilationUnit cu = parseSample("AClassWithFields");
        ClassOrInterfaceDeclaration classC = Navigator.demandClass(cu, "C");
        TypeDeclaration typeDeclaration = JavaParserFacade.get(new JreTypeSolver()).getTypeDeclaration(classC);
        assertEquals(3, typeDeclaration.getAllFields().size());
        assertEquals(ImmutableSet.of("a", "b", "c"),
                typeDeclaration.getAllFields().stream().map(Declaration::getName).collect(Collectors.toSet()));
    }
}
