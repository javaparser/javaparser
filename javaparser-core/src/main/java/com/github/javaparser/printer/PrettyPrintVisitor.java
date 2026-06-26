/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
package com.github.javaparser.printer;

import static com.github.javaparser.ast.Node.Parsedness.UNPARSABLE;
import static com.github.javaparser.utils.PositionUtils.sortByBeginPosition;
import static com.github.javaparser.utils.Utils.*;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.PrettyPrinterConfiguration;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Outputs the AST as formatted Java source code.
 * This class is no longer acceptable to use because it is not sufficiently configurable and it is too tied to a specific implementation
 * <p> Use {@link DefaultPrettyPrinterVisitor default implementation } instead.
 *
 * <p>The bulk of the printing logic is inherited from {@link DefaultPrettyPrinterVisitor}; only the
 * deprecated public API and the handful of node types whose output historically differed from the
 * maintained visitor are kept here, so the two implementations no longer duplicate ~1900 lines of
 * code. See <a href="https://github.com/javaparser/javaparser/issues/4914">issue #4914</a>.
 *
 * @author Julio Vilmar Gesser
 * @deprecated This class is no longer acceptable to use because it is not sufficiently configurable and it is too tied to a specific implementation.
 * This class could be removed in a future version. Use default DefaultPrettyPrinterVisitor.
 */
@Deprecated
public class PrettyPrintVisitor extends DefaultPrettyPrinterVisitor {

    public PrettyPrintVisitor(PrettyPrinterConfiguration prettyPrinterConfiguration) {
        super(prettyPrinterConfiguration);
    }

    public void setConfiguration(PrettyPrinterConfiguration prettyPrinterConfiguration) {
        this.configuration = prettyPrinterConfiguration;
    }

    /**
     * @deprecated use toString()
     */
    @Deprecated
    public String getSource() {
        return printer.toString();
    }

    /*
     * The methods below intentionally preserve the historical behaviour of this deprecated visitor,
     * which differs from {@link DefaultPrettyPrinterVisitor}. All other node types are inherited.
     */

    @Override
    public void visit(final ArrayInitializerExpr n, final Void arg) {
        printOrphanCommentsBeforeThisChildNode(n);
        printComment(n.getComment(), arg);
        printer.print("{");
        if (!isNullOrEmpty(n.getValues())) {
            printer.print(" ");
            for (final Iterator<Expression> i = n.getValues().iterator(); i.hasNext(); ) {
                final Expression expr = i.next();
                expr.accept(this, arg);
                if (i.hasNext()) {
                    printer.print(", ");
                }
            }
            printer.print(" ");
        }
        printOrphanCommentsEnding(n);
        printer.print("}");
    }

    @Override
    public void visit(final CompilationUnit n, final Void arg) {
        printOrphanCommentsBeforeThisChildNode(n);
        printComment(n.getComment(), arg);
        if (n.getParsed() == UNPARSABLE) {
            printer.println("???");
            return;
        }
        if (n.getPackageDeclaration().isPresent()) {
            n.getPackageDeclaration().get().accept(this, arg);
        }
        n.getImports().accept(this, arg);
        if (!n.getImports().isEmpty()) {
            printer.println();
        }
        for (final Iterator<TypeDeclaration<?>> i = n.getTypes().iterator(); i.hasNext(); ) {
            i.next().accept(this, arg);
            printer.println();
            if (i.hasNext()) {
                printer.println();
            }
        }
        n.getModule().ifPresent(m -> m.accept(this, arg));
        printOrphanCommentsEnding(n);
    }

    @Override
    public void visit(final ConstructorDeclaration n, final Void arg) {
        printOrphanCommentsBeforeThisChildNode(n);
        printComment(n.getComment(), arg);
        printMemberAnnotations(n.getAnnotations(), arg);
        printModifiers(n.getModifiers());
        printTypeParameters(n.getTypeParameters(), arg);
        if (n.isGeneric()) {
            printer.print(" ");
        }
        n.getName().accept(this, arg);
        printer.print("(");
        if (!n.getParameters().isEmpty()) {
            for (final Iterator<Parameter> i = n.getParameters().iterator(); i.hasNext(); ) {
                final Parameter p = i.next();
                p.accept(this, arg);
                if (i.hasNext()) {
                    printer.print(", ");
                }
            }
        }
        printer.print(")");
        if (!isNullOrEmpty(n.getThrownExceptions())) {
            printer.print(" throws ");
            for (final Iterator<ReferenceType> i = n.getThrownExceptions().iterator(); i.hasNext(); ) {
                final ReferenceType name = i.next();
                name.accept(this, arg);
                if (i.hasNext()) {
                    printer.print(", ");
                }
            }
        }
        printer.print(" ");
        n.getBody().accept(this, arg);
    }

    @Override
    protected void printOrphanCommentsEnding(final Node node) {
        if (!getOption(ConfigOption.PRINT_COMMENTS).isPresent()) return;
        // extract all nodes for which the position/range is indicated to avoid to skip orphan comments
        List<Node> everything =
                node.getChildNodes().stream().filter(n -> n.hasRange()).collect(Collectors.toList());
        sortByBeginPosition(everything);
        if (everything.isEmpty()) {
            return;
        }
        int commentsAtEnd = 0;
        boolean findingComments = true;
        while (findingComments && commentsAtEnd < everything.size()) {
            Node last = everything.get(everything.size() - 1 - commentsAtEnd);
            findingComments = (last instanceof Comment);
            if (findingComments) {
                commentsAtEnd++;
            }
        }
        for (int i = 0; i < commentsAtEnd; i++) {
            everything.get(everything.size() - commentsAtEnd + i).accept(this, null);
        }
    }
}
