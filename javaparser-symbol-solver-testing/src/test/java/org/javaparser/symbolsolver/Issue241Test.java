/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package org.javaparser.symbolsolver;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.ast.type.Type;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue241Test extends AbstractResolutionTest{

    @Test
    void testSolveStaticallyImportedMemberType() {
        Path src = adaptPath("src/test/resources");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        		
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
