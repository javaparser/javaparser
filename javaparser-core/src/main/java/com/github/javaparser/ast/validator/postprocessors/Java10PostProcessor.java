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
package com.github.javaparser.ast.validator.postprocessors;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Processor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VarType;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Processes the generic AST into a Java 10 AST and validates it.
 */
public class Java10PostProcessor extends PostProcessors {

    // List of parent contexts in which a var type must not be detected.
    // for example: in this statement var.class.getCanonicalName(), var must not be considered as a VarType
    private static List<Class> FORBIDEN_PARENT_CONTEXT_TO_DETECT_POTENTIAL_VAR_TYPE = new ArrayList<>();

    static {
        FORBIDEN_PARENT_CONTEXT_TO_DETECT_POTENTIAL_VAR_TYPE.addAll(Arrays.asList(ClassExpr.class));
    }

    protected final Processor varNodeCreator = new Processor() {

        @Override
        public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
            result.getResult().ifPresent(node -> {
                node.findAll(ClassOrInterfaceType.class).forEach(n -> {
                    if (n.getNameAsString().equals("var") && !matchForbiddenContext(n)) {
                        n.replace(new VarType(n.getTokenRange().orElse(null)));
                    }
                });
            });
        }

        private boolean matchForbiddenContext(ClassOrInterfaceType cit) {
            return cit.getParentNode().isPresent() && FORBIDEN_PARENT_CONTEXT_TO_DETECT_POTENTIAL_VAR_TYPE.stream().anyMatch(cl -> cl.isInstance(cit.getParentNode().get()));
        }
    };

    public Java10PostProcessor() {
        add(varNodeCreator);
    }
}
