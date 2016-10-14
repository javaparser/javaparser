package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import static org.junit.Assert.*;


public class JavaParserFacadeResolutionTest extends AbstractResolutionTest {

    @Test
    public void typeDeclarationSuperClassImplicitlyIncludeObject() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        TypeDeclaration typeDeclaration = JavaParserFacade.get(new JreTypeSolver()).getTypeDeclaration(clazz);
        ReferenceType superclass = typeDeclaration.asClass().getSuperClass();
        assertEquals(Object.class.getCanonicalName(), superclass.getQualifiedName());
    }
}
