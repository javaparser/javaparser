/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class ModifierVisitorGenerator extends VisitorGenerator {
    public ModifierVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "ModifierVisitor", "Visitable", "A", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        // FIXME: Bit of a hacky way to get this fixed order, and then have everything else (note this list is reversed)
        List<String> order = Arrays.asList(
//                "comment", "name", "members", "parameters", "name",
                "modifiers", "annotations"
        );
        List<PropertyMetaModel> sortedPropertyMetaModels = node.getAllPropertyMetaModels()
                .stream()
                .sorted(Comparator
                        .comparingInt((PropertyMetaModel o) -> order.indexOf(o.getName())).reversed()
//                        .thenComparing(PropertyMetaModel::getName)
                )
                .collect(Collectors.toList());

        //
        sortedPropertyMetaModels.forEach(property -> extracted(body, property));

        //
        if (node.is(BinaryExpr.class)) {
            body.addStatement("if (left == null) return right;");
            body.addStatement("if (right == null) return left;");
        } else {
            final SeparatedItemStringBuilder collapseCheck = new SeparatedItemStringBuilder("if(", "||", ") return null;");
            sortedPropertyMetaModels.forEach(property -> {
                if (property.isRequired() && property.isNode()) {
                    if (property.isNodeList()) {
                        if (property.isNonEmpty()) {
                            collapseCheck.append(f("%s.isEmpty()", property.getName()));
                        }
                    } else {
                        collapseCheck.append(f("%s==null", property.getName()));
                    }
                }
            });
            if (collapseCheck.hasItems()) {
                body.addStatement(collapseCheck.toString());
            }
        }

        //
        sortedPropertyMetaModels.forEach(property -> {
            if (property.isNode()) {
                body.addStatement(f("n.%s(%s);", property.getSetterMethodName(), property.getName()));
            }
        });

        //
        body.addStatement("return n;");
    }

    private void extracted(BlockStmt body, PropertyMetaModel property) {
        if (property.isNode()) {
            if (property.isNodeList()) {
                body.addStatement(f("NodeList<%s> %s = modifyList(n.%s(), arg);",
                        property.getTypeNameGenerified(),
                        property.getName(),
                        property.getGetterMethodName()));
            } else if (property.isOptional()) {
                body.addStatement(f("%s %s = n.%s().map(s -> (%s) s.accept(this, arg)).orElse(null);",
                        property.getTypeNameGenerified(),
                        property.getName(),
                        property.getGetterMethodName(),
                        property.getTypeNameGenerified()));
            } else {
                body.addStatement(f("%s %s = (%s) n.%s().accept(this, arg);",
                        property.getTypeNameGenerified(),
                        property.getName(),
                        property.getTypeNameGenerified(),
                        property.getGetterMethodName()));
            }
        }
    }
}
