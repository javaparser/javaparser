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

package com.github.javaparser.generator.core.node;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

import static com.github.javaparser.StaticJavaParser.parseExplicitConstructorInvocationStmt;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class MainConstructorGenerator extends NodeGenerator {
    public MainConstructorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        if (nodeMetaModel.is(Node.class)) {
            return;
        }
        ConstructorDeclaration constructor = new ConstructorDeclaration()
                .setPublic(true)
                .setName(nodeCoid.getNameAsString())
                .addParameter(TokenRange.class, "tokenRange")
                .setJavadocComment("\n     * This constructor is used by the parser and is considered private.\n     ");

        BlockStmt body = constructor.getBody();

        SeparatedItemStringBuilder superCall = new SeparatedItemStringBuilder("super(", ", ", ");");
        superCall.append("tokenRange");
        for (PropertyMetaModel parameter : nodeMetaModel.getConstructorParameters()) {
            constructor.addParameter(parameter.getTypeNameForSetter(), parameter.getName());
            if (nodeMetaModel.getDeclaredPropertyMetaModels().contains(parameter)) {
                body.addStatement(f("%s(%s);", parameter.getSetterMethodName(), parameter.getName()));
            } else {
                superCall.append(parameter.getName());
            }
        }

        body.getStatements().addFirst(parseExplicitConstructorInvocationStmt(superCall.toString()));

        body.addStatement("customInitialization();");

        addOrReplaceWhenSameSignature(nodeCoid, constructor);
        nodeCu.addImport(TokenRange.class);
    }
}
