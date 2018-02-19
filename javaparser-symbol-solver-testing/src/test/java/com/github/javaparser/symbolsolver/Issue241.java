package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.assertEquals;

public class Issue241 extends AbstractResolutionTest{

    @Test
    public void testSolveStaticallyImportedMemberType() {
        File src = adaptPath(new File("src/test/resources"));
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(src));
        		
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        
        CompilationUnit cu = parseSample("Issue241");
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "Main");
        VariableDeclarator v = Navigator.demandVariableDeclaration(cls, "foo").get();
        
        Type t = v.getType();
        ResolvedType t2 = javaParserFacade.convert(t, t);
        String typeName = t2.asReferenceType().getQualifiedName();
       
        assertEquals("issue241.TypeWithMemberType.MemberInterface", typeName);
    }
}
