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

package com.github.javaparser.printer.concretesyntaxmodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.printer.SourcePrinter;

public class CsmComment implements CsmElement {

    static void process(Comment comment, SourcePrinter printer) {
        String content = printer.normalizeEolInTextBlock(comment.getContent());
        if (comment instanceof BlockComment) {
            printer.print("/*");
            printer.print(content);
            printer.println("*/");
        } else if (comment instanceof JavadocComment) {
            printer.print("/**");
            printer.print(content);
            printer.println("*/");
        } else if (comment instanceof LineComment) {
            printer.print("//");
            printer.print(content);
            printer.println();
        } else {
            throw new UnsupportedOperationException(comment.getClass().getSimpleName());
        }
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        node.getComment().ifPresent(c -> process(c, printer));
    }

}
