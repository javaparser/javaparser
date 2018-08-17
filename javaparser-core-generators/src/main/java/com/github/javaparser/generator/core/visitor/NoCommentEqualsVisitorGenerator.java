/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.generator.core.visitor;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SourceRoot;

public class NoCommentEqualsVisitorGenerator extends VisitorGenerator {

    public NoCommentEqualsVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "NoCommentEqualsVisitor", "Boolean", "Visitable", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod,
                                           CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        if (!(node.equals(JavaParserMetaModel.lineCommentMetaModel)
                || node.equals(JavaParserMetaModel.blockCommentMetaModel)
                || node.equals(JavaParserMetaModel.javadocCommentMetaModel))) {

            body.addStatement(f("final %s n2 = (%s) arg;", node.getTypeName(), node.getTypeName()));

            for (PropertyMetaModel field : node.getAllPropertyMetaModels()) {
                final String getter = field.getGetterMethodName() + "()";
                if (field.equals(JavaParserMetaModel.nodeMetaModel.commentPropertyMetaModel))
                    continue;
                if (field.getNodeReference().isPresent()) {
                    if (field.isNodeList()) {
                        body.addStatement(f("if (!nodesEquals(n.%s, n2.%s)) return false;", getter, getter));
                    } else {
                        body.addStatement(f("if (!nodeEquals(n.%s, n2.%s)) return false;", getter, getter));
                    }
                } else {
                    body.addStatement(f("if (!objEquals(n.%s, n2.%s)) return false;", getter, getter));
                }
            }
            if (body.getStatements().size() == 1) {
                // Only the cast line was added, but nothing is using it, so remove it again.
                body.getStatements().clear();
            }
        }
        body.addStatement("return true;");
    }
}