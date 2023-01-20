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
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SourceRoot;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Generates JavaParser's GenericListVisitorAdapter.
 */
public class GenericListVisitorAdapterGenerator extends VisitorGenerator {
    public GenericListVisitorAdapterGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "GenericListVisitorAdapter", "List<R>", "A", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();
        body.addStatement("List<R> result = new ArrayList<>();");
        body.addStatement("List<R> tmp;");

        final String resultCheck = "if (tmp != null) result.addAll(tmp);";

        for (PropertyMetaModel field : node.getAllPropertyMetaModels()) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isOptional()) {
                    body.addStatement(f("if (n.%s.isPresent()) {" +
                            "   tmp = n.%s.get().accept(this, arg);" +
                            "   %s" +
                            "}", getter, getter, resultCheck));
                } else {
                    body.addStatement(f("{ tmp = n.%s.accept(this, arg); %s }", getter, resultCheck));
                }
            }
        }
        body.addStatement("return result;");
        Arrays.stream(new Class<?>[] {List.class, ArrayList.class}).filter(c ->
                compilationUnit.getImports().stream().noneMatch(
                        i -> c.getName().equals(i.getName().asString())
                )
        ).forEach(compilationUnit::addImport);
    }
}
