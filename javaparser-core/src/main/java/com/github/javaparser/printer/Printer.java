/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.printer;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.lexical.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Iterator;
import java.util.List;

import static com.github.javaparser.ast.lexical.LexemeKind.*;
import static com.github.javaparser.ast.lexical.WhitespaceKind.LINE_ENDING;
import static com.github.javaparser.ast.lexical.WhitespaceKind.NORMAL;
import static com.github.javaparser.printer.FormatterSettings.EmptyLineLocation.*;
import static com.github.javaparser.printer.FormatterSettings.IndentationContext.*;

/**
 * @author Didier Villevalois
 */
public class Printer {

    /**
     * Prints the specified node to a string.
     *
     * @param node the node to print
     * @return the node printed to a string
     */
    public static String printToString(Node node) {
        StringWriter writer = new StringWriter();
        printTo(node, new PrintWriter(writer));
        return writer.toString();
    }

    /**
     * Prints the specified node to the specified writer.
     *
     * @param node   the node to print
     * @param writer the writer to print to
     */
    public static void printTo(Node node, PrintWriter writer) {
        Printer printer = new Printer(writer, false);
        printer.print(node);
    }

    private final PrintWriter writer;
    private final boolean format;
    private final FormatterSettings settings;

    /**
     * Creates a Printer that prints to the specified writer with no formatting and the default formatter settings.
     *
     * @param writer the writer to print to
     */
    public Printer(PrintWriter writer) {
        this(writer, false, FormatterSettings.DEFAULT);
    }

    /**
     * Creates a Printer that prints to the specified writer with the default formatter settings.
     *
     * @param writer the writer to print to
     * @param format whether to format printed nodes
     */
    public Printer(PrintWriter writer, boolean format) {
        this(writer, format, FormatterSettings.DEFAULT);
    }

    /**
     * Creates a Printer that prints to the specified writer with the specified formatter settings.
     *
     * @param writer   the writer to print to
     * @param settings whether to format printed nodes
     */
    public Printer(PrintWriter writer, FormatterSettings settings) {
        this(writer, true, settings);
    }

    /**
     * Creates a Printer that prints to the specified writer with the specified formatter settings.
     *
     * @param writer   the writer to print to
     * @param format   whether to format printed nodes
     * @param settings whether to format printed nodes
     */
    public Printer(PrintWriter writer, boolean format, FormatterSettings settings) {
        this.writer = writer;
        this.format = format;
        this.settings = FormatterSettings.DEFAULT;
    }

    /**
     * Prints the specified node.
     *
     * @param node the node to print
     */
    public void print(Node node) {
        printVisitor.print(node);
    }

    private PrintVisitor printVisitor = new PrintVisitor();

    private abstract class PrintController implements VoidVisitor<Void> {

        private int indentLevel;
        private int delayedIndentation;
        private boolean needsIndentation;
        private Lexeme current;
        private boolean afterNewContent;
        private boolean afterAlpha;

        public void print(Node node) {
            reset();

            // TODO Use extendedFirst() to pick leading comments
            Lexeme first = node.first();
            if (first == null) {
                afterNewContent = true;
            }

            current = first;
            printNode(node);

            // TODO Use extendedLast() to pick trailing comment
            Lexeme last = node.last();
            if (!format && last != null && current != null && last.next() != current) {
                consumeUntil(last);
            }
        }

        private void reset() {
            indentLevel = 0;
            needsIndentation = true;
            afterNewContent = false;
            afterAlpha = false;
        }

        protected void printNode(Node node) {
            afterNewContent = false;
            Lexeme oldCurrent = current;
            Lexeme first = node.first();

            if (first == null) {
                current = null;
            }

            while (followingIsDanglingCommentsAndEmptyLine()) {
                consumeDanglingCommentsAndEmptyLine();
            }

            CommentAttributes commentAttributes = node.getCommentAttributes();
            if (commentAttributes != null) {
                List<Comment> leadingComments = commentAttributes.getLeadingComments();
                if (leadingComments != null) {
                    for (Comment comment : leadingComments) {
                        printLeadingComment(comment);
                    }
                }
            }

            node.accept(this, null);

            if (commentAttributes != null) {
                Comment trailingComment = commentAttributes.getTrailingComment();
                if (trailingComment != null) {
                    printTrailingComment(trailingComment);
                }
            }

            if (first == null) {
                current = oldCurrent;
                afterNewContent = true;
            }
        }

        private void consumeUntil(Lexeme target) {
            while (current != null && current != target) {
                writer.append(current.image());
                current = current.next();
            }
        }

        private boolean followingIsEmptyLine() {
            Lexeme search = current;
            while (search != null) {
                if (!search.is(WHITESPACE))
                    return false;
                if (search.is(LINE_ENDING))
                    return true;
                search = search.next();
            }
            return false;
        }

        private Lexeme emptyEndOfLine() {
            Lexeme search = current;
            while (search != null) {
                if (!search.is(WHITESPACE))
                    return null;
                if (search.is(LINE_ENDING))
                    return search;
                search = search.next();
            }
            return null;
        }

        private boolean followingIsComment() {
            Lexeme search = current;
            while (search != null) {
                if (search.is(COMMENT))
                    return true;
                if (!search.is(WHITESPACE) || search.is(LINE_ENDING))
                    return false;
                search = search.next();
            }
            return false;
        }

        private boolean followingIsComment(Comment comment) {
            Lexeme search = current;
            while (search != null) {
                if (search == comment)
                    return true;
                if (!search.is(WHITESPACE))
                    return false;
                search = search.next();
            }
            return false;
        }

        private boolean followingIsDanglingCommentsAndEmptyLine() {
            Lexeme search = current;
            boolean inEmptyLine = true;
            while (search != null) {
                if (search.is(COMMENT)) {
                    inEmptyLine = false;
                } else if (search.is(WHITESPACE)) {
                    if (search.is(LINE_ENDING)) {
                        if (inEmptyLine) return true;
                        inEmptyLine = true;
                    }
                } else {
                    return false;
                }
                search = search.next();
            }
            return false;
        }

        private void consumeDanglingCommentsAndEmptyLine() {
            boolean inEmptyLine = true;
            while (current != null) {
                if (!followingIsEmptyLine()) printIndentIfNecessary();
                if (current.is(COMMENT)) {
                    writer.append(current.image());
                    current = current.next();
                    inEmptyLine = false;
                } else if (current.is(WHITESPACE)) {
                    if (current.is(LINE_ENDING)) {
                        printNewLine();
                        if (inEmptyLine) {
                            return;
                        }
                        inEmptyLine = true;
                    } else {
                        consumeWhitespace(NORMAL);
                    }
                } else {
                    throw new IllegalStateException();
                }
            }
        }

        private boolean consumeWhitespace(WhitespaceKind kind) {
            if (current != null) {
                if (!(current.is(WHITESPACE) && current.is(kind)))
                    return false;
                if (!format) writer.append(current.image());
                current = current.next();
            }
            return false;
        }

        private void consumeEndOfLine() {
            if (current != null) {
                Lexeme emptyEndOfLine = emptyEndOfLine();
                if (emptyEndOfLine != null) {
                    if (format) {
                        doPrintNewLine("\n");
                        current = emptyEndOfLine.next();
                    } else {
                        consumeUntil(emptyEndOfLine.next());
                    }
                } else {
                    if (current.is(WHITESPACE) && current.is(LINE_ENDING)) {
                        if (format) {
                            writer.append("\n");
                        } else {
                            writer.append(current.image());
                        }
                        current = current.next();
                    } else if (current.is(COMMENT)) {
                        writer.append(current.image());
                        current = current.next();
                    } else {
                        if (format || afterAlpha) {
                            writer.append("\n");
                        }
                    }
                }
            } else {
                writer.append("\n");
            }
            needsIndentation = true;
        }

        private void consumeCommentsAndWhitespace(String minimalSpace, boolean nextIsAlpha) {
            if (current != null) {
                if (!(current.is(COMMENT) || current.is(WHITESPACE)) && ((afterAlpha && nextIsAlpha) || format)) {
                    writer.append(minimalSpace);
                } else {
                    while (current != null) {
                        if ((!current.is(COMMENT) && !current.is(WHITESPACE)))
                            break;

                        int emptyLines = 0;
                        Lexeme emptyEndOfLine = emptyEndOfLine();
                        if (emptyEndOfLine != null) {
                            if (format) {
                                doPrintNewLine("\n");
                                current = emptyEndOfLine.next();
                            } else {
                                consumeUntil(emptyEndOfLine.next());
                            }
                            needsIndentation = true;
                        } else {
                            if (current.is(WHITESPACE)) {
                                if (format) {
                                    writer.append(minimalSpace);
                                } else {
                                    writer.append(current.image());
                                }
                            } else if (current.is(COMMENT)) {
                                writer.append(current.image());
                            } else {
                                if (format || afterAlpha) {
                                    writer.append(minimalSpace);
                                }
                            }

                            current = current.next();
                        }
                    }
                }
            } else {
                writer.append(minimalSpace);
            }
            afterAlpha = false;
        }

        private void consumeIdentifier(String image) {
            if (current != null) {
                if (!current.is(IDENTIFIER) || !current.image().equals(image))
                    throw new IllegalStateException();
                current = current.next();
            }
            writer.append(image);
            afterAlpha = true;
        }

        private void consumeLiteral(LiteralKind kind, String image) {
            if (current != null) {
                if (!current.is(LITERAL) || !current.is(kind) || !current.image().equals(image))
                    throw new IllegalStateException();
                current = current.next();
            }
            writer.append(image);
        }

        private void consumeKeyword(KeywordKind kind) {
            if (current != null) {
                if (!current.is(KEYWORD) || !current.is(kind))
                    throw new IllegalStateException();
                current = current.next();
            }
            writer.append(kind.image);
            afterAlpha = true;
        }

        private void consumeOperator(OperatorKind kind) {
            if (current != null) {
                if (!current.is(OPERATOR) || !current.is(kind))
                    throw new IllegalStateException();
                current = current.next();
            }
            writer.append(kind.image);
        }

        private void consumeSeparator(SeparatorKind kind) {
            if (current != null) {
                if (!current.is(SEPARATOR) || !current.is(kind))
                    throw new IllegalStateException();
                current = current.next();
            }
            writer.append(kind.image);
        }

        protected void printNewLine() {
            if (!followingIsComment()) {
                consumeEndOfLine();
            }
        }

        protected void printEmptyLines(int emptyLineCount) {
            for (int i = 0; i < emptyLineCount; i++) {
                if (followingIsEmptyLine()) {
                    printNewLine();
                } else if (format || afterNewContent || current == null) {
                    doPrintNewLine("\n");
                }
            }
        }

        private void doPrintNewLine(String image) {
            writer.append(image);
            needsIndentation = true;
        }

        protected void indent(int indentation) {
            indentLevel += indentation;
        }

        protected void delayedIndent(int indentation) {
            delayedIndentation = indentation;
        }

        protected void unIndent(int indentation) {
            indentLevel -= indentation;
        }

        private void printIndentIfNecessary() {
            if (needsIndentation) {
                boolean consumed = consumeWhitespace(NORMAL);
                if (((current == null || format) && !(consumed || format)) || format) {
                    doPrintIndent();
                }
                needsIndentation = false;
            }
            indentLevel += delayedIndentation;
            delayedIndentation = 0;
        }

        private void doPrintIndent() {
            for (int i = 0; i < indentLevel; i++) {
                writer.append("    ");
            }
        }

        protected void printSpace() {
            consumeCommentsAndWhitespace(" ", false);
        }

        protected void printLeadingComment(Comment comment) {
            boolean followingIsComment = followingIsComment(comment);
            if (current != null && followingIsComment) {
                printIndentIfNecessary();
                writer.append(comment.image());
                current = current.next();
                if (comment.is(CommentKind.SINGLE_LINE)) {
                    printNewLine();
                }
            } else if (!followingIsComment) {
                doPrintIndent();
                writer.append(comment.image());
                doPrintNewLine("\n");
            } else {
                printIndentIfNecessary();
                writer.append(comment.image());
            }
        }

        protected void printTrailingComment(Comment comment) {
            boolean followingIsComment = followingIsComment(comment);
            if (current != null && followingIsComment) {
                // Read a space
                if (current.is(WHITESPACE) && current.is(NORMAL)) {
                    writer.append(current.image());
                    current = current.next();
                }

                writer.append(comment.image());
                current = current.next();

                if (comment.is(CommentKind.SINGLE_LINE)) {
                    printNewLine();
                }
            } else {
                writer.append(" ");
                writer.append(comment.image());
            }
        }

        protected void printIdentifier(String image) {
            consumeCommentsAndWhitespace("", true);
            printIndentIfNecessary();
            consumeIdentifier(image);
        }

        protected void printLiteral(LiteralKind kind, String image) {
            consumeCommentsAndWhitespace("", false);
            printIndentIfNecessary();
            consumeLiteral(kind, image);
        }

        protected void printKeyword(KeywordKind kind) {
            consumeCommentsAndWhitespace("", true);
            printIndentIfNecessary();
            consumeKeyword(kind);
        }

        protected void printOperator(OperatorKind kind) {
            consumeCommentsAndWhitespace("", false);
            printIndentIfNecessary();
            consumeOperator(kind);
        }

        protected void printSeparator(SeparatorKind kind) {
            consumeCommentsAndWhitespace("", false);
            printIndentIfNecessary();
            consumeSeparator(kind);
        }

        protected void printModifiers(List<KeywordKind> modifiers) {
            consumeCommentsAndWhitespace("", true);
            printIndentIfNecessary();
            if (current != null) {
                while (current != null && !modifiers.isEmpty()) {
                    if (current.is(KEYWORD)) {
                        KeywordKind keywordKind = ((Keyword) current).getKeywordKind();
                        if (modifiers.contains(keywordKind)) {
                            modifiers.remove(keywordKind);

                            consumeKeyword(keywordKind);
                            printSpace();
                        } else {
                            // Removed modifier
                            current = current.next();
                        }
                    } else {
                        break;
                    }
                }
            }

            if (!modifiers.isEmpty()) {
                for (KeywordKind modifier : modifiers) {
                    printKeyword(modifier);
                    printSpace();
                }
            }
        }
    }

    public class PrintVisitor extends PrintController {

        private void printModifiers(final int modifiers) {
            List<KeywordKind> modifierKeywords = new ArrayList<KeywordKind>();

            if (ModifierSet.isPrivate(modifiers)) {
                modifierKeywords.add(KeywordKind.PRIVATE);
            }
            if (ModifierSet.isProtected(modifiers)) {
                modifierKeywords.add(KeywordKind.PROTECTED);
            }
            if (ModifierSet.isPublic(modifiers)) {
                modifierKeywords.add(KeywordKind.PUBLIC);
            }
            if (ModifierSet.isAbstract(modifiers)) {
                modifierKeywords.add(KeywordKind.ABSTRACT);
            }
            if (ModifierSet.isStatic(modifiers)) {
                modifierKeywords.add(KeywordKind.STATIC);
            }
            if (ModifierSet.isDefault(modifiers)) {
                modifierKeywords.add(KeywordKind.DEFAULT);
            }
            if (ModifierSet.isFinal(modifiers)) {
                modifierKeywords.add(KeywordKind.FINAL);
            }
            if (ModifierSet.isNative(modifiers)) {
                modifierKeywords.add(KeywordKind.NATIVE);
            }
            if (ModifierSet.isStrictfp(modifiers)) {
                modifierKeywords.add(KeywordKind.STRICTFP);
            }
            if (ModifierSet.isSynchronized(modifiers)) {
                modifierKeywords.add(KeywordKind.SYNCHRONIZED);
            }
            if (ModifierSet.isTransient(modifiers)) {
                modifierKeywords.add(KeywordKind.TRANSIENT);
            }
            if (ModifierSet.isVolatile(modifiers)) {
                modifierKeywords.add(KeywordKind.VOLATILE);
            }

            printModifiers(modifierKeywords);
        }

        private void printMembers(final List<BodyDeclaration> members) {
            printEmptyLines(settings.emptyLineCount(BEFORE_MEMBERS));
            for (final Iterator<BodyDeclaration> i = members.iterator(); i.hasNext(); ) {
                final BodyDeclaration member = i.next();
                printNode(member);
                if (i.hasNext()) {
                    printEmptyLines(settings.emptyLineCount(BETWEEN_MEMBERS));
                }
            }
            printEmptyLines(settings.emptyLineCount(AFTER_MEMBERS));
        }

        private void printMemberAnnotations(final List<AnnotationExpr> annotations) {
            if (annotations != null) {
                for (final AnnotationExpr a : annotations) {
                    printNode(a);
                    printNewLine();
                }
            }
        }

        private void printAnnotations(final List<AnnotationExpr> annotations) {
            if (annotations != null) {
                for (final AnnotationExpr a : annotations) {
                    printNode(a);
                    printSpace();
                }
            }
        }

        private void printTypeArgs(final List<Type> args) {
            if (args != null) {
                if (args.isEmpty()) {
                    printOperator(OperatorKind.DIAMOND);
                } else {
                    printOperator(OperatorKind.LT);
                    for (final Iterator<Type> i = args.iterator(); i.hasNext(); ) {
                        final Type t = i.next();
                        printNode(t);
                        if (i.hasNext()) {
                            printSeparator(SeparatorKind.COMMA);
                            printSpace();
                        }
                    }
                    printOperator(OperatorKind.GT);
                }
            }
        }

        private void printTypeParameters(final List<TypeParameter> args) {
            if (args != null) {
                printOperator(OperatorKind.LT);
                for (final Iterator<TypeParameter> i = args.iterator(); i.hasNext(); ) {
                    final TypeParameter t = i.next();
                    printNode(t);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
                printOperator(OperatorKind.GT);
            }
        }

        private void printArguments(final List<Expression> args) {
            printSeparator(SeparatorKind.LPAREN);
            if (args != null) {
                for (final Iterator<Expression> i = args.iterator(); i.hasNext(); ) {
                    final Expression e = i.next();
                    printNode(e);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            printSeparator(SeparatorKind.RPAREN);
        }

        private void printParameters(List<Parameter> parameters) {
            printSeparator(SeparatorKind.LPAREN);
            if (parameters != null) {
                for (final Iterator<Parameter> i = parameters.iterator(); i.hasNext(); ) {
                    final Parameter p = i.next();
                    printNode(p);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            printSeparator(SeparatorKind.RPAREN);
        }

        @Override
        public void visit(final CompilationUnit n, final Void arg) {
            if (n.getPackage() != null) {
                printNode(n.getPackage());
                printEmptyLines(settings.emptyLineCount(AFTER_PACKAGE_DECLARATION));
            }

            if (n.getImports() != null) {
                for (final ImportDeclaration i : n.getImports()) {
                    printNode(i);
                }
                printEmptyLines(settings.emptyLineCount(AFTER_IMPORT_DECLARATIONS));
            }

            if (n.getTypes() != null) {
                for (final Iterator<TypeDeclaration> i = n.getTypes().iterator(); i.hasNext(); ) {
                    printNode(i.next());
                    if (i.hasNext()) {
                        printEmptyLines(settings.emptyLineCount(BETWEEN_TOP_LEVEL_DECLARATIONS));
                    }
                }
            }
        }

        @Override
        public void visit(final PackageDeclaration n, final Void arg) {
            printAnnotations(n.getAnnotations());
            printKeyword(KeywordKind.PACKAGE);
            printSpace();
            printNode(n.getName());
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final NameExpr n, final Void arg) {
            printIdentifier(n.getName());
        }

        @Override
        public void visit(final QualifiedNameExpr n, final Void arg) {
            printNode(n.getQualifier());
            printSeparator(SeparatorKind.DOT);
            printIdentifier(n.getName());
        }

        @Override
        public void visit(final ImportDeclaration n, final Void arg) {
            printKeyword(KeywordKind.IMPORT);
            printSpace();
            if (n.isStatic()) {
                printKeyword(KeywordKind.STATIC);
                printSpace();
            }
            printNode(n.getName());
            if (n.isAsterisk()) {
                printSeparator(SeparatorKind.DOT);
                printOperator(OperatorKind.STAR);
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final ClassOrInterfaceDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());

            if (n.isInterface()) {
                printKeyword(KeywordKind.INTERFACE);
                printSpace();
            } else {
                printKeyword(KeywordKind.CLASS);
                printSpace();
            }

            printIdentifier(n.getName());

            printTypeParameters(n.getTypeParameters());

            if (n.getExtends() != null) {
                printSpace();
                printKeyword(KeywordKind.EXTENDS);
                printSpace();
                for (final Iterator<ClassOrInterfaceType> i = n.getExtends().iterator(); i.hasNext(); ) {
                    final ClassOrInterfaceType c = i.next();
                    printNode(c);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }

            if (n.getImplements() != null) {
                printSpace();
                printKeyword(KeywordKind.IMPLEMENTS);
                printSpace();
                for (final Iterator<ClassOrInterfaceType> i = n.getImplements().iterator(); i.hasNext(); ) {
                    final ClassOrInterfaceType c = i.next();
                    printNode(c);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }

            printSpace();
            printSeparator(SeparatorKind.LBRACE);
            printNewLine();
            indent(settings.indentation(TYPE_BODY));
            if (n.getMembers() != null) {
                printMembers(n.getMembers());
            }

            unIndent(settings.indentation(TYPE_BODY));
            printSeparator(SeparatorKind.RBRACE);
            printNewLine();
        }

        @Override
        public void visit(final EmptyTypeDeclaration n, final Void arg) {
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final ClassOrInterfaceType n, final Void arg) {
            if (n.getAnnotations() != null) {
                for (AnnotationExpr ae : n.getAnnotations()) {
                    printNode(ae);
                    printSpace();
                }
            }

            if (n.getScope() != null) {
                printNode(n.getScope());
                printSeparator(SeparatorKind.DOT);
            }
            printIdentifier(n.getName());
            printTypeArgs(n.getTypeArgs());
        }

        @Override
        public void visit(final TypeParameter n, final Void arg) {
            if (n.getAnnotations() != null) {
                for (AnnotationExpr ann : n.getAnnotations()) {
                    printNode(ann);
                    printSpace();
                }
            }
            printIdentifier(n.getName());
            if (n.getTypeBound() != null) {
                printSpace();
                printKeyword(KeywordKind.EXTENDS);
                printSpace();
                for (final Iterator<ClassOrInterfaceType> i = n.getTypeBound().iterator(); i.hasNext(); ) {
                    final ClassOrInterfaceType c = i.next();
                    printNode(c);
                    if (i.hasNext()) {
                        printSpace();
                        printOperator(OperatorKind.BIT_AND);
                        printSpace();
                    }
                }
            }
        }

        @Override
        public void visit(final PrimitiveType n, final Void arg) {
            if (n.getAnnotations() != null) {
                for (AnnotationExpr ae : n.getAnnotations()) {
                    printNode(ae);
                    printSpace();
                }
            }
            switch (n.getType()) {
                case Boolean:
                    printKeyword(KeywordKind.BOOLEAN);
                    break;
                case Byte:
                    printKeyword(KeywordKind.BYTE);
                    break;
                case Char:
                    printKeyword(KeywordKind.CHAR);
                    break;
                case Double:
                    printKeyword(KeywordKind.DOUBLE);
                    break;
                case Float:
                    printKeyword(KeywordKind.FLOAT);
                    break;
                case Int:
                    printKeyword(KeywordKind.INT);
                    break;
                case Long:
                    printKeyword(KeywordKind.LONG);
                    break;
                case Short:
                    printKeyword(KeywordKind.SHORT);
                    break;
            }
        }

        @Override
        public void visit(final ReferenceType n, final Void arg) {
            if (n.getAnnotations() != null) {
                for (AnnotationExpr ae : n.getAnnotations()) {
                    printNode(ae);
                    printSpace();
                }
            }
            printNode(n.getType());
            List<List<AnnotationExpr>> arraysAnnotations = n.getArraysAnnotations();
            for (int i = 0; i < n.getArrayCount(); i++) {
                if (arraysAnnotations != null && i < arraysAnnotations.size()) {
                    List<AnnotationExpr> annotations = arraysAnnotations.get(i);
                    if (annotations != null) {
                        for (AnnotationExpr ae : annotations) {
                            printSpace();
                            printNode(ae);

                        }
                    }
                }
                printSeparator(SeparatorKind.LBRACKET);
                printSeparator(SeparatorKind.RBRACKET);
            }
        }

        @Override
        public void visit(final WildcardType n, final Void arg) {
            if (n.getAnnotations() != null) {
                for (AnnotationExpr ae : n.getAnnotations()) {
                    printSpace();
                    printNode(ae);
                }
            }
            printOperator(OperatorKind.HOOK);
            if (n.getExtends() != null) {
                printSpace();
                printKeyword(KeywordKind.EXTENDS);
                printSpace();
                printNode(n.getExtends());
            }
            if (n.getSuper() != null) {
                printSpace();
                printKeyword(KeywordKind.SUPER);
                printSpace();
                printNode(n.getSuper());
            }
        }

        @Override
        public void visit(final FieldDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());
            printNode(n.getType());

            printSpace();
            for (final Iterator<VariableDeclarator> i = n.getVariables().iterator(); i.hasNext(); ) {
                final VariableDeclarator var = i.next();
                printNode(var);
                if (i.hasNext()) {
                    printSeparator(SeparatorKind.COMMA);
                    printSpace();
                }
            }

            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final VariableDeclarator n, final Void arg) {
            printNode(n.getId());
            if (n.getInit() != null) {
                printSpace();
                printOperator(OperatorKind.ASSIGN);
                printSpace();
                printNode(n.getInit());
            }
        }

        @Override
        public void visit(final VariableDeclaratorId n, final Void arg) {
            printIdentifier(n.getName());
            for (int i = 0; i < n.getArrayCount(); i++) {
                printSeparator(SeparatorKind.LBRACKET);
                printSeparator(SeparatorKind.RBRACKET);
            }
        }

        @Override
        public void visit(final ArrayInitializerExpr n, final Void arg) {
            printSeparator(SeparatorKind.LBRACE);
            if (n.getValues() != null) {
                printSpace();
                for (final Iterator<Expression> i = n.getValues().iterator(); i.hasNext(); ) {
                    final Expression expr = i.next();
                    printNode(expr);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
                printSpace();
            }
            printSeparator(SeparatorKind.RBRACE);
        }

        @Override
        public void visit(final VoidType n, final Void arg) {
            printKeyword(KeywordKind.VOID);
        }

        @Override
        public void visit(final ArrayAccessExpr n, final Void arg) {
            printNode(n.getName());
            printSeparator(SeparatorKind.LBRACKET);
            printNode(n.getIndex());
            printSeparator(SeparatorKind.RBRACKET);
        }

        @Override
        public void visit(final ArrayCreationExpr n, final Void arg) {
            printKeyword(KeywordKind.NEW);
            printSpace();
            printNode(n.getType());
            List<List<AnnotationExpr>> arraysAnnotations = n.getArraysAnnotations();
            if (n.getDimensions() != null) {
                int j = 0;
                for (final Expression dim : n.getDimensions()) {

                    if (arraysAnnotations != null && j < arraysAnnotations.size()) {
                        List<AnnotationExpr> annotations = arraysAnnotations.get(j);
                        if (annotations != null) {
                            for (AnnotationExpr ae : annotations) {
                                printSpace();
                                printNode(ae);
                            }
                        }
                    }
                    printSeparator(SeparatorKind.LBRACKET);
                    printNode(dim);
                    printSeparator(SeparatorKind.RBRACKET);
                    j++;
                }
                for (int i = 0; i < n.getArrayCount(); i++) {
                    if (arraysAnnotations != null && i < arraysAnnotations.size()) {

                        List<AnnotationExpr> annotations = arraysAnnotations.get(i);
                        if (annotations != null) {
                            for (AnnotationExpr ae : annotations) {
                                printSpace();
                                printNode(ae);

                            }
                        }
                    }
                    printSeparator(SeparatorKind.LBRACKET);
                    printSeparator(SeparatorKind.RBRACKET);
                }

            } else {
                for (int i = 0; i < n.getArrayCount(); i++) {
                    if (arraysAnnotations != null && i < arraysAnnotations.size()) {
                        List<AnnotationExpr> annotations = arraysAnnotations.get(i);
                        if (annotations != null) {
                            for (AnnotationExpr ae : annotations) {
                                printNode(ae);
                                printSpace();
                            }
                        }
                    }
                    printSeparator(SeparatorKind.LBRACKET);
                    printSeparator(SeparatorKind.RBRACKET);
                }
                printSpace();
                printNode(n.getInitializer());
            }
        }

        @Override
        public void visit(final AssignExpr n, final Void arg) {
            printNode(n.getTarget());
            printSpace();
            switch (n.getOperator()) {
                case assign:
                    printOperator(OperatorKind.ASSIGN);
                    break;
                case and:
                    printOperator(OperatorKind.ANDASSIGN);
                    break;
                case or:
                    printOperator(OperatorKind.ORASSIGN);
                    break;
                case xor:
                    printOperator(OperatorKind.XORASSIGN);
                    break;
                case plus:
                    printOperator(OperatorKind.PLUSASSIGN);
                    break;
                case minus:
                    printOperator(OperatorKind.MINUSASSIGN);
                    break;
                case rem:
                    printOperator(OperatorKind.REMASSIGN);
                    break;
                case slash:
                    printOperator(OperatorKind.SLASHASSIGN);
                    break;
                case star:
                    printOperator(OperatorKind.STARASSIGN);
                    break;
                case lShift:
                    printOperator(OperatorKind.LSHIFTASSIGN);
                    break;
                case rSignedShift:
                    printOperator(OperatorKind.RSIGNEDSHIFTASSIGN);
                    break;
                case rUnsignedShift:
                    printOperator(OperatorKind.RUNSIGNEDSHIFTASSIGN);
                    break;
            }
            printSpace();
            printNode(n.getValue());
        }

        @Override
        public void visit(final BinaryExpr n, final Void arg) {
            printNode(n.getLeft());
            printSpace();
            switch (n.getOperator()) {
                case or:
                    printOperator(OperatorKind.SC_OR);
                    break;
                case and:
                    printOperator(OperatorKind.SC_AND);
                    break;
                case binOr:
                    printOperator(OperatorKind.BIT_OR);
                    break;
                case binAnd:
                    printOperator(OperatorKind.BIT_AND);
                    break;
                case xor:
                    printOperator(OperatorKind.XOR);
                    break;
                case equals:
                    printOperator(OperatorKind.EQ);
                    break;
                case notEquals:
                    printOperator(OperatorKind.NE);
                    break;
                case less:
                    printOperator(OperatorKind.LT);
                    break;
                case greater:
                    printOperator(OperatorKind.GT);
                    break;
                case lessEquals:
                    printOperator(OperatorKind.LE);
                    break;
                case greaterEquals:
                    printOperator(OperatorKind.GE);
                    break;
                case lShift:
                    printOperator(OperatorKind.LSHIFT);
                    break;
                case rSignedShift:
                    printOperator(OperatorKind.RSIGNEDSHIFT);
                    break;
                case rUnsignedShift:
                    printOperator(OperatorKind.RUNSIGNEDSHIFT);
                    break;
                case plus:
                    printOperator(OperatorKind.PLUS);
                    break;
                case minus:
                    printOperator(OperatorKind.MINUS);
                    break;
                case times:
                    printOperator(OperatorKind.STAR);
                    break;
                case divide:
                    printOperator(OperatorKind.SLASH);
                    break;
                case remainder:
                    printOperator(OperatorKind.REM);
                    break;
            }
            printSpace();
            printNode(n.getRight());
        }

        @Override
        public void visit(final CastExpr n, final Void arg) {
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getType());
            printSeparator(SeparatorKind.RPAREN);
            printSpace();
            printNode(n.getExpr());
        }

        @Override
        public void visit(final ClassExpr n, final Void arg) {
            printNode(n.getType());
            printSeparator(SeparatorKind.DOT);
            printKeyword(KeywordKind.CLASS);
        }

        @Override
        public void visit(final ConditionalExpr n, final Void arg) {
            printNode(n.getCondition());
            printSpace();
            printOperator(OperatorKind.HOOK);
            printSpace();
            printNode(n.getThenExpr());
            printSpace();
            printOperator(OperatorKind.COLON);
            printSpace();
            printNode(n.getElseExpr());
        }

        @Override
        public void visit(final EnclosedExpr n, final Void arg) {
            printSeparator(SeparatorKind.LPAREN);
            if (n.getInner() != null) {
                printNode(n.getInner());
            }
            printSeparator(SeparatorKind.RPAREN);
        }

        @Override
        public void visit(final FieldAccessExpr n, final Void arg) {
            printNode(n.getScope());
            printSeparator(SeparatorKind.DOT);
            printIdentifier(n.getField());
        }

        @Override
        public void visit(final InstanceOfExpr n, final Void arg) {
            printNode(n.getExpr());
            printSpace();
            printKeyword(KeywordKind.INSTANCEOF);
            printSpace();
            printNode(n.getType());
        }

        @Override
        public void visit(final CharLiteralExpr n, final Void arg) {
            printLiteral(LiteralKind.CHARACTER, "'" + n.getValue() + "'");
        }

        @Override
        public void visit(final DoubleLiteralExpr n, final Void arg) {
            printLiteral(LiteralKind.FLOATING_POINT, n.getValue());
        }

        @Override
        public void visit(final IntegerLiteralExpr n, final Void arg) {
            String value = n.getValue();
            if (value.startsWith("-")) {
                printOperator(OperatorKind.MINUS);
                printLiteral(LiteralKind.INTEGER, value.substring(1));
            } else {
                printLiteral(LiteralKind.INTEGER, value);
            }
        }

        @Override
        public void visit(final LongLiteralExpr n, final Void arg) {
            String value = n.getValue();
            if (value.startsWith("-")) {
                printOperator(OperatorKind.MINUS);
                printLiteral(LiteralKind.LONG, value.substring(1));
            } else {
                printLiteral(LiteralKind.LONG, value);
            }
        }

        @Override
        public void visit(final IntegerLiteralMinValueExpr n, final Void arg) {
            visit((IntegerLiteralExpr) n, arg);
        }

        @Override
        public void visit(final LongLiteralMinValueExpr n, final Void arg) {
            visit((LongLiteralExpr) n, arg);
        }

        @Override
        public void visit(final StringLiteralExpr n, final Void arg) {
            printLiteral(LiteralKind.STRING, "\"" + n.getValue() + "\"");
        }

        @Override
        public void visit(final BooleanLiteralExpr n, final Void arg) {
            if (n.getValue()) printKeyword(KeywordKind.TRUE);
            else printKeyword(KeywordKind.FALSE);
        }

        @Override
        public void visit(final NullLiteralExpr n, final Void arg) {
            printKeyword(KeywordKind.NULL);
        }

        @Override
        public void visit(final ThisExpr n, final Void arg) {
            if (n.getClassExpr() != null) {
                printNode(n.getClassExpr());
                printSeparator(SeparatorKind.DOT);
            }
            printKeyword(KeywordKind.THIS);
        }

        @Override
        public void visit(final SuperExpr n, final Void arg) {
            if (n.getClassExpr() != null) {
                printNode(n.getClassExpr());
                printSeparator(SeparatorKind.DOT);
            }
            printKeyword(KeywordKind.SUPER);
        }

        @Override
        public void visit(final MethodCallExpr n, final Void arg) {
            if (n.getScope() != null) {
                printNode(n.getScope());
                printSeparator(SeparatorKind.DOT);
            }
            printTypeArgs(n.getTypeArgs());
            printIdentifier(n.getName());
            printArguments(n.getArgs());
        }

        @Override
        public void visit(final ObjectCreationExpr n, final Void arg) {
            if (n.getScope() != null) {
                printNode(n.getScope());
                printSeparator(SeparatorKind.DOT);
            }

            printKeyword(KeywordKind.NEW);
            printSpace();

            printTypeArgs(n.getTypeArgs());
            printSpace();

            printNode(n.getType());

            printArguments(n.getArgs());

            if (n.getAnonymousClassBody() != null) {
                printSpace();
                printSeparator(SeparatorKind.LBRACE);
                printNewLine();
                indent(settings.indentation(TYPE_BODY));
                printMembers(n.getAnonymousClassBody());
                unIndent(settings.indentation(TYPE_BODY));
                printSeparator(SeparatorKind.RBRACE);
            }
        }

        @Override
        public void visit(final UnaryExpr n, final Void arg) {
            switch (n.getOperator()) {
                case positive:
                    printOperator(OperatorKind.PLUS);
                    break;
                case negative:
                    printOperator(OperatorKind.MINUS);
                    break;
                case inverse:
                    printOperator(OperatorKind.TILDE);
                    break;
                case not:
                    printOperator(OperatorKind.BANG);
                    break;
                case preIncrement:
                    printOperator(OperatorKind.INCR);
                    break;
                case preDecrement:
                    printOperator(OperatorKind.DECR);
                    break;
                default:
            }

            printNode(n.getExpr());

            switch (n.getOperator()) {
                case posIncrement:
                    printOperator(OperatorKind.INCR);
                    break;
                case posDecrement:
                    printOperator(OperatorKind.DECR);
                    break;
                default:
            }
        }

        @Override
        public void visit(final ConstructorDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());

            printTypeParameters(n.getTypeParameters());
            if (n.getTypeParameters() != null) {
                printSpace();
            }
            printIdentifier(n.getName());

            printParameters(n.getParameters());

            if (n.getThrows() != null && !n.getThrows().isEmpty()) {
                printSpace();
                printKeyword(KeywordKind.THROWS);
                printSpace();
                for (final Iterator<NameExpr> i = n.getThrows().iterator(); i.hasNext(); ) {
                    final NameExpr name = i.next();
                    printNode(name);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            printSpace();
            printNode(n.getBlock());
        }

        @Override
        public void visit(final MethodDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());
            printTypeParameters(n.getTypeParameters());
            if (n.getTypeParameters() != null) {
                printSpace();
            }

            printNode(n.getType());
            printSpace();
            printIdentifier(n.getName());

            printParameters(n.getParameters());

            for (int i = 0; i < n.getArrayCount(); i++) {
                printSeparator(SeparatorKind.LBRACKET);
                printSeparator(SeparatorKind.RBRACKET);
            }

            if (n.getThrows() != null && !n.getThrows().isEmpty()) {
                printSpace();
                printKeyword(KeywordKind.THROWS);
                printSpace();
                for (final Iterator<NameExpr> i = n.getThrows().iterator(); i.hasNext(); ) {
                    final NameExpr name = i.next();
                    printNode(name);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            if (n.getBody() == null) {
                printSeparator(SeparatorKind.SEMICOLON);
            } else {
                printSpace();
                printNode(n.getBody());
            }
            printNewLine();
        }

        @Override
        public void visit(final Parameter n, final Void arg) {
            printAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());
            if (n.getType() != null) {
                printNode(n.getType());
            }
            if (n.isVarArgs()) {
                printOperator(OperatorKind.ELLIPSIS);
            }
            printSpace();
            printNode(n.getId());
        }

        @Override
        public void visit(final MultiTypeParameter n, final Void arg) {
            printAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());

            Iterator<Type> types = n.getTypes().iterator();
            printNode(types.next());
            while (types.hasNext()) {
                printSpace();
                printOperator(OperatorKind.BIT_OR);
                printSpace();
                printNode(types.next());
            }

            printSpace();
            printNode(n.getId());
        }

        @Override
        public void visit(final ExplicitConstructorInvocationStmt n, final Void arg) {
            if (n.isThis()) {
                printTypeArgs(n.getTypeArgs());
                printKeyword(KeywordKind.THIS);
            } else {
                if (n.getExpr() != null) {
                    printNode(n.getExpr());
                    printSeparator(SeparatorKind.DOT);
                }
                printTypeArgs(n.getTypeArgs());
                printKeyword(KeywordKind.SUPER);
            }
            printArguments(n.getArgs());
            printSeparator(SeparatorKind.SEMICOLON);
        }

        @Override
        public void visit(final VariableDeclarationExpr n, final Void arg) {
            printAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());

            printNode(n.getType());
            printSpace();

            for (final Iterator<VariableDeclarator> i = n.getVars().iterator(); i.hasNext(); ) {
                final VariableDeclarator v = i.next();
                printNode(v);
                if (i.hasNext()) {
                    printSeparator(SeparatorKind.COMMA);
                    printSpace();
                }
            }
        }

        @Override
        public void visit(final TypeDeclarationStmt n, final Void arg) {
            printNode(n.getTypeDeclaration());
        }

        @Override
        public void visit(final AssertStmt n, final Void arg) {
            printKeyword(KeywordKind.ASSERT);
            printSpace();
            printNode(n.getCheck());
            if (n.getMessage() != null) {
                printSpace();
                printOperator(OperatorKind.COLON);
                printSpace();
                printNode(n.getMessage());
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final BlockStmt n, final Void arg) {
            printSeparator(SeparatorKind.LBRACE);
            printNewLine();
            if (n.getStmts() != null) {
                indent(settings.indentation(BLOCK));
                for (final Statement s : n.getStmts()) {
                    printNode(s);
                }
                unIndent(settings.indentation(BLOCK));
            }
            printSeparator(SeparatorKind.RBRACE);
        }

        @Override
        public void visit(final LabeledStmt n, final Void arg) {
            printIdentifier(n.getLabel());
            printOperator(OperatorKind.COLON);
            printSpace();
            printNode(n.getStmt());
        }

        @Override
        public void visit(final EmptyStmt n, final Void arg) {
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();

        }

        @Override
        public void visit(final ExpressionStmt n, final Void arg) {
            delayedIndent(settings.indentation(STATEMENT));
            printNode(n.getExpression());
            if (!(n.getParentNode() instanceof LambdaExpr)) {
                printSeparator(SeparatorKind.SEMICOLON);
                printNewLine();
            }
            unIndent(settings.indentation(STATEMENT));
        }

        @Override
        public void visit(final SwitchStmt n, final Void arg) {
            printKeyword(KeywordKind.SWITCH);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getSelector());
            printSeparator(SeparatorKind.RPAREN);
            printSpace();
            printSeparator(SeparatorKind.LBRACE);
            if (n.getEntries() != null) {
                indent(settings.indentation(SWITCH));
                for (final SwitchEntryStmt e : n.getEntries()) {
                    printNode(e);
                }
                unIndent(settings.indentation(SWITCH));
            }
            printSeparator(SeparatorKind.RBRACE);

        }

        @Override
        public void visit(final SwitchEntryStmt n, final Void arg) {
            if (n.getLabel() != null) {
                printKeyword(KeywordKind.CASE);
                printSpace();
                printNode(n.getLabel());
                printOperator(OperatorKind.COLON);
            } else {
                printKeyword(KeywordKind.DEFAULT);
                printOperator(OperatorKind.COLON);
            }
            printNewLine();
            indent(settings.indentation(SWITCH_CASE));
            if (n.getStmts() != null) {
                for (final Statement s : n.getStmts()) {
                    printNode(s);
                    printNewLine();
                }
            }
            unIndent(settings.indentation(SWITCH_CASE));
        }

        @Override
        public void visit(final BreakStmt n, final Void arg) {
            printKeyword(KeywordKind.BREAK);
            if (n.getId() != null) {
                printSpace();
                printIdentifier(n.getId());
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final ReturnStmt n, final Void arg) {
            delayedIndent(settings.indentation(STATEMENT));
            printKeyword(KeywordKind.RETURN);
            if (n.getExpr() != null) {
                printSpace();
                printNode(n.getExpr());
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
            unIndent(settings.indentation(STATEMENT));
        }

        @Override
        public void visit(final EnumDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());

            printKeyword(KeywordKind.ENUM);
            printSpace();
            printIdentifier(n.getName());

            if (n.getImplements() != null) {
                printSpace();
                printKeyword(KeywordKind.IMPLEMENTS);
                printSpace();
                for (final Iterator<ClassOrInterfaceType> i = n.getImplements().iterator(); i.hasNext(); ) {
                    final ClassOrInterfaceType c = i.next();
                    printNode(c);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }

            printSpace();
            printSeparator(SeparatorKind.LBRACE);
            printNewLine();
            indent(settings.indentation(TYPE_BODY));
            if (n.getEntries() != null) {
                printNewLine();
                for (final Iterator<EnumConstantDeclaration> i = n.getEntries().iterator(); i.hasNext(); ) {
                    final EnumConstantDeclaration e = i.next();
                    printNode(e);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            if (n.getMembers() != null) {
                printSeparator(SeparatorKind.SEMICOLON);
                printNewLine();

                printMembers(n.getMembers());
            } else {
                if (n.getEntries() != null) {
                    printNewLine();
                }
            }
            unIndent(settings.indentation(TYPE_BODY));
            printSeparator(SeparatorKind.RBRACE);
            printNewLine();
        }

        @Override
        public void visit(final EnumConstantDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printIdentifier(n.getName());

            if (n.getArgs() != null) {
                printArguments(n.getArgs());
            }

            if (n.getClassBody() != null) {
                printSpace();
                printSeparator(SeparatorKind.LBRACE);
                printNewLine();
                indent(settings.indentation(TYPE_BODY));
                printMembers(n.getClassBody());
                unIndent(settings.indentation(TYPE_BODY));
                printSeparator(SeparatorKind.RBRACE);
                printNewLine();
            }
        }

        @Override
        public void visit(final EmptyMemberDeclaration n, final Void arg) {
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final InitializerDeclaration n, final Void arg) {
            if (n.isStatic()) {
                printKeyword(KeywordKind.STATIC);
                printSpace();
            }
            printNode(n.getBlock());
            printNewLine();
        }

        @Override
        public void visit(final IfStmt n, final Void arg) {
            printKeyword(KeywordKind.IF);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getCondition());
            printSeparator(SeparatorKind.RPAREN);

            final boolean thenBlock = n.getThenStmt() instanceof BlockStmt;
            if (thenBlock) {
                // block statement should start on the same line
                printSpace();
            } else {
                printNewLine();
                indent(settings.indentation(IF_ELSE));
            }
            printNode(n.getThenStmt());
            if (!thenBlock)
                unIndent(settings.indentation(IF_ELSE));
            if (n.getElseStmt() != null) {
                if (thenBlock)
                    printSpace();
                else
                    printNewLine();
                final boolean elseIf = n.getElseStmt() instanceof IfStmt;
                final boolean elseBlock = n.getElseStmt() instanceof BlockStmt;
                printKeyword(KeywordKind.ELSE);
                if (elseIf || elseBlock) {
                    // put chained if and start of block statement on a same level
                    printSpace();
                } else {
                    printNewLine();
                    indent(settings.indentation(IF_ELSE));
                }
                printNode(n.getElseStmt());
                if (!(elseIf || elseBlock))
                    unIndent(settings.indentation(IF_ELSE));
            }
        }

        @Override
        public void visit(final WhileStmt n, final Void arg) {
            printKeyword(KeywordKind.WHILE);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getCondition());
            printSeparator(SeparatorKind.RPAREN);
            printSpace();
            printNode(n.getBody());
            printNewLine();
        }

        @Override
        public void visit(final ContinueStmt n, final Void arg) {
            printKeyword(KeywordKind.CONTINUE);
            if (n.getId() != null) {
                printSpace();
                printIdentifier(n.getId());
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final DoStmt n, final Void arg) {
            printKeyword(KeywordKind.DO);
            printSpace();
            printNode(n.getBody());
            printSpace();
            printKeyword(KeywordKind.WHILE);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getCondition());
            printSeparator(SeparatorKind.RPAREN);
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final ForeachStmt n, final Void arg) {
            printKeyword(KeywordKind.FOR);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getVariable());
            printSpace();
            printOperator(OperatorKind.COLON);
            printSpace();
            printNode(n.getIterable());
            printSeparator(SeparatorKind.RPAREN);
            printSpace();
            printNode(n.getBody());
            printNewLine();
        }

        @Override
        public void visit(final ForStmt n, final Void arg) {
            printKeyword(KeywordKind.FOR);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            if (n.getInit() != null) {
                for (final Iterator<Expression> i = n.getInit().iterator(); i.hasNext(); ) {
                    final Expression e = i.next();
                    printNode(e);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printSpace();
            if (n.getCompare() != null) {
                printNode(n.getCompare());
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printSpace();
            if (n.getUpdate() != null) {
                for (final Iterator<Expression> i = n.getUpdate().iterator(); i.hasNext(); ) {
                    final Expression e = i.next();
                    printNode(e);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            printSeparator(SeparatorKind.RPAREN);
            printSpace();
            printNode(n.getBody());
            printNewLine();
        }

        @Override
        public void visit(final ThrowStmt n, final Void arg) {
            printKeyword(KeywordKind.THROW);
            printSpace();
            printNode(n.getExpr());
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final SynchronizedStmt n, final Void arg) {
            printKeyword(KeywordKind.SYNCHRONIZED);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getExpr());
            printSeparator(SeparatorKind.RPAREN);
            printSpace();
            printNode(n.getBlock());
        }

        @Override
        public void visit(final TryStmt n, final Void arg) {
            printKeyword(KeywordKind.TRY);
            printSpace();
            if (!n.getResources().isEmpty()) {
                printSeparator(SeparatorKind.LPAREN);
                Iterator<VariableDeclarationExpr> resources = n.getResources().iterator();
                boolean first = true;
                while (resources.hasNext()) {
                    visit(resources.next(), arg);
                    if (resources.hasNext()) {
                        printSeparator(SeparatorKind.SEMICOLON);
                        printNewLine();
                        if (first) {
                            indent(settings.indentation(TRY_RESOURCES));
                        }
                    }
                    first = false;
                }
                if (n.getResources().size() > 1) {
                    unIndent(settings.indentation(TRY_RESOURCES));
                }
                printSeparator(SeparatorKind.RPAREN);
                printSpace();
            }
            printNode(n.getTryBlock());
            if (n.getCatchs() != null) {
                for (final CatchClause c : n.getCatchs()) {
                    printNode(c);
                }
            }
            if (n.getFinallyBlock() != null) {
                printSpace();
                printKeyword(KeywordKind.FINALLY);
                printSpace();
                printNode(n.getFinallyBlock());
            }
        }

        @Override
        public void visit(final CatchClause n, final Void arg) {
            printSpace();
            printKeyword(KeywordKind.CATCH);
            printSpace();
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getExcept());
            printSeparator(SeparatorKind.RPAREN);
            printSpace();
            printNode(n.getCatchBlock());

        }

        @Override
        public void visit(final AnnotationDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());

            printSeparator(SeparatorKind.AT);
            printKeyword(KeywordKind.INTERFACE);
            printSpace();
            printIdentifier(n.getName());
            printSpace();
            printSeparator(SeparatorKind.LBRACE);
            printNewLine();
            indent(settings.indentation(TYPE_BODY));
            if (n.getMembers() != null) {
                printMembers(n.getMembers());
            }
            unIndent(settings.indentation(TYPE_BODY));
            printSeparator(SeparatorKind.RBRACE);
            printNewLine();
        }

        @Override
        public void visit(final AnnotationMemberDeclaration n, final Void arg) {
            printMemberAnnotations(n.getAnnotations());
            printModifiers(n.getModifiers());

            printNode(n.getType());
            printSpace();
            printIdentifier(n.getName());
            printSeparator(SeparatorKind.LPAREN);
            printSeparator(SeparatorKind.RPAREN);
            if (n.getDefaultValue() != null) {
                printSpace();
                printKeyword(KeywordKind.DEFAULT);
                printSpace();
                printNode(n.getDefaultValue());
            }
            printSeparator(SeparatorKind.SEMICOLON);
            printNewLine();
        }

        @Override
        public void visit(final MarkerAnnotationExpr n, final Void arg) {
            printSeparator(SeparatorKind.AT);
            printNode(n.getName());
        }

        @Override
        public void visit(final SingleMemberAnnotationExpr n, final Void arg) {
            printSeparator(SeparatorKind.AT);
            printNode(n.getName());
            printSeparator(SeparatorKind.LPAREN);
            printNode(n.getMemberValue());
            printSeparator(SeparatorKind.RPAREN);
        }

        @Override
        public void visit(final NormalAnnotationExpr n, final Void arg) {
            printSeparator(SeparatorKind.AT);
            printNode(n.getName());
            printSeparator(SeparatorKind.LPAREN);
            if (n.getPairs() != null) {
                for (final Iterator<MemberValuePair> i = n.getPairs().iterator(); i.hasNext(); ) {
                    final MemberValuePair m = i.next();
                    printNode(m);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            printSeparator(SeparatorKind.RPAREN);
        }

        @Override
        public void visit(final MemberValuePair n, final Void arg) {
            printIdentifier(n.getName());
            printSpace();
            printOperator(OperatorKind.ASSIGN);
            printSpace();
            printNode(n.getValue());
        }

        @Override
        public void visit(final LambdaExpr n, final Void arg) {

            List<Parameter> parameters = n.getParameters();
            boolean printPar = false;
            printPar = n.isParametersEnclosed();

            if (printPar) {
                printSeparator(SeparatorKind.LPAREN);
            }
            if (parameters != null) {
                for (Iterator<Parameter> i = parameters.iterator(); i.hasNext(); ) {
                    Parameter p = i.next();
                    printNode(p);
                    if (i.hasNext()) {
                        printSeparator(SeparatorKind.COMMA);
                        printSpace();
                    }
                }
            }
            if (printPar) {
                printSeparator(SeparatorKind.RPAREN);
            }

            printOperator(OperatorKind.ARROW);
            printNode(n.getBody());
        }

        @Override
        public void visit(final MethodReferenceExpr n, final Void arg) {
            Expression scope = n.getScope();
            String identifier = n.getIdentifier();
            if (scope != null) {
                printNode(n.getScope());
            }

            printOperator(OperatorKind.DOUBLECOLON);
            printTypeParameters(n.getTypeParameters());
            if (identifier != null) {
                printIdentifier(identifier);
            }

        }

        @Override
        public void visit(final TypeExpr n, final Void arg) {
            if (n.getType() != null) {
                printNode(n.getType());
            }
        }
    }
}
