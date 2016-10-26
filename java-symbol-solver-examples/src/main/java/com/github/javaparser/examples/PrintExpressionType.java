/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.examples;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

public class PrintExpressionType {


    static class TypeCalculatorVisitor extends VoidVisitorAdapter<JavaParserFacade> {
        @Override
        public void visit(ReturnStmt n, JavaParserFacade javaParserFacade) {
            super.visit(n, javaParserFacade);
            //System.out.println(n.getExpr().toString() + " has type " + javaParserFacade.getType(n.getExpr()));
        }

        @Override
        public void visit(MethodCallExpr n, JavaParserFacade javaParserFacade) {
            super.visit(n, javaParserFacade);
            System.out.println(n.toString() + " has type " + javaParserFacade.getType(n).describe());
            if (javaParserFacade.getType(n).isReferenceType()) {
                for (ReferenceType ancestor : javaParserFacade.getType(n).asReferenceType().getAllAncestors()) {
                    //System.out.println("Ancestor " + ancestor.describe());
                }
            }
        }
    }

    public static void main(String[] args) throws FileNotFoundException, ParseException {
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(new File("java-symbol-solver-examples/src/main/resources/someproject")));

        CompilationUnit agendaCu = JavaParser.parse(new FileInputStream(new File("java-symbol-solver-examples/src/main/resources/someproject/me/tomassetti/Agenda.java")));

        agendaCu.accept(new TypeCalculatorVisitor(), JavaParserFacade.get(typeSolver));

    }

}
