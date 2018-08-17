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

import static com.github.javaparser.JavaParser.parseStatement;

import java.util.List;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

public class NoCommentHashCodeVisitorGenerator extends VisitorGenerator {

    public NoCommentHashCodeVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "NoCommentHashCodeVisitor", "Integer", "Void", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod,
                                           CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        final BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        final SeparatedItemStringBuilder builder = new SeparatedItemStringBuilder("return ", "* 31 +", ";");
        final List<PropertyMetaModel> propertyMetaModels = node.getAllPropertyMetaModels();
        if (node.equals(JavaParserMetaModel.lineCommentMetaModel)
                || node.equals(JavaParserMetaModel.blockCommentMetaModel)
                || node.equals(JavaParserMetaModel.javadocCommentMetaModel) || propertyMetaModels.isEmpty()) {
            builder.append("0");
        } else {
            for (PropertyMetaModel field : propertyMetaModels) {
                final String getter = field.getGetterMethodName() + "()";
                if (field.equals(JavaParserMetaModel.nodeMetaModel.commentPropertyMetaModel)) {
                    if (propertyMetaModels.size() == 1) {
                        builder.append("0");
                        break;
                    } else
                        continue;
                }
                // Is this field another AST node? Visit it.
                if (field.getNodeReference().isPresent()) {
                    if (field.isOptional()) {
                        builder.append("(n.%s.isPresent()? n.%s.get().accept(this, arg):0)", getter, getter);
                    } else {
                        builder.append("(n.%s.accept(this, arg))", getter);
                    }
                } else {
                    Class<?> type = field.getType();
                    if (type.equals(boolean.class)) {
                        builder.append("(n.%s?1:0)", getter);
                    } else if (type.equals(int.class)) {
                        builder.append("n.%s", getter);
                    } else {
                        builder.append("(n.%s.hashCode())", getter);
                    }
                }
            }
        }
        body.addStatement(parseStatement(builder.toString()));
    }
}
