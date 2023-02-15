/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests resolution of FieldAccessExpr with same names in scope and identifier
 *
 * @author Takeshi D. Itoh
 */
class FieldAccessExprResolutionTest extends AbstractResolutionTest {

    @BeforeEach
    void configureSymbolSolver() throws IOException {
        // configure symbol solver so as not to potentially disturb tests in other classes
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
    }

    @Test
    void solveX() throws IOException {
        CompilationUnit cu = parseSample("FieldAccessExprResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Main");
        MethodDeclaration md = Navigator.demandMethod(clazz, "x");
        MethodCallExpr mce = Navigator.findMethodCall(md, "method").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("X.method", actual);
    }

    @Test
    void solveXX() throws IOException {
        CompilationUnit cu = parseSample("FieldAccessExprResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Main");
        MethodDeclaration md = Navigator.demandMethod(clazz, "x_x");
        MethodCallExpr mce = Navigator.findMethodCall(md, "method").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("X.X1.method", actual);
    }

    @Test
    void solveXYX() throws IOException {
        CompilationUnit cu = parseSample("FieldAccessExprResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Main");
        MethodDeclaration md = Navigator.demandMethod(clazz, "x_y_x");
        MethodCallExpr mce = Navigator.findMethodCall(md, "method").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("X.Y1.X2.method", actual);
    }

    @Test
    void solveXYZX() throws IOException {
        CompilationUnit cu = parseSample("FieldAccessExprResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Main");
        MethodDeclaration md = Navigator.demandMethod(clazz, "x_z_y_x");
        MethodCallExpr mce = Navigator.findMethodCall(md, "method").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("X.Z1.Y2.X3.method", actual);
    }

}
