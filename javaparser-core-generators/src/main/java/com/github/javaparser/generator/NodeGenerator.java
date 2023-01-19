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

package com.github.javaparser.generator;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.util.Arrays;

/**
 * Makes it easier to generate code in the core AST nodes. The generateNode method will get every node type passed to
 * it, ready for modification.
 */
public abstract class NodeGenerator extends Generator {
    protected NodeGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    public final void generate() throws Exception {
        Log.info("Running %s", () -> getClass().getSimpleName());
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            Pair<CompilationUnit, ClassOrInterfaceDeclaration> result = parseNode(nodeMetaModel);
            generateNode(nodeMetaModel, result.a, result.b);
        }
        after();
    }

    protected Pair<CompilationUnit, ClassOrInterfaceDeclaration> parseNode(BaseNodeMetaModel nodeMetaModel) {
        CompilationUnit nodeCu = sourceRoot.parse(nodeMetaModel.getPackageName(), nodeMetaModel.getTypeName() + ".java");
        ClassOrInterfaceDeclaration nodeCoid = nodeCu.getClassByName(nodeMetaModel.getTypeName()).orElseThrow(() -> new AssertionError("Can't find class"));
        return new Pair<>(nodeCu, nodeCoid);
    }

    /**
     * Annotate a method with the {@link Override} annotation, if it overrides other method.
     *
     * @param nodeMetaModel     The current meta model.
     * @param methodDeclaration The method declaration.
     */
    protected void annotateWhenOverridden(BaseNodeMetaModel nodeMetaModel, MethodDeclaration methodDeclaration) {
        Class<? extends Node> type = nodeMetaModel.getType();
        Class<?> superClass = type.getSuperclass();

        boolean isOverriding = Arrays.stream(superClass.getMethods())
                .filter(m -> m.getName().equals(methodDeclaration.getNameAsString()))
                .anyMatch(m -> m.getParameters().length == methodDeclaration.getParameters().size());
        if (isOverriding) {
            annotateOverridden(methodDeclaration);
        }
    }

    protected void after() throws Exception {

    }

    protected abstract void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) throws Exception;
}
