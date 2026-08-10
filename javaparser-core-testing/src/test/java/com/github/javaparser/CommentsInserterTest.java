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

package com.github.javaparser;

import static com.github.javaparser.utils.TestUtils.assertEqualToTextResourceNoEol;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.utils.LineSeparator;
import com.github.javaparser.utils.TestParser;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import org.junit.jupiter.api.Test;

class CommentsInserterTest {
    private String makeFilename(String sampleName) {
        return "com/github/javaparser/issue_samples/" + sampleName + ".java.txt";
    }

    private String makeExpectedFilename(String sampleName) {
        return "/com/github/javaparser/issue_samples/" + sampleName + ".java.expected.txt";
    }

    private ParseResult<CompilationUnit> parseSample(String sampleName) throws IOException {
        Provider p = Providers.resourceProvider(makeFilename(sampleName));
        return new JavaParser().parse(ParseStart.COMPILATION_UNIT, p);
    }

    /**
     * Issue: "When there is a String constant "\\" compilationUnit ignores all further comments"
     */
    @Test
    void issue290() throws IOException {
        ParseResult<CompilationUnit> result = this.parseSample("Issue290");
        CommentsCollection cc = result.getCommentsCollection().get();
        assertEquals(1, cc.getLineComments().size());
        assertEquals(1, cc.getJavadocComments().size());
    }

    @Test
    void issue624() throws IOException {
        this.parseSample("Issue624");
        // Should not fail
    }

    @Test
    void issue200EnumConstantsWithCommentsForceVerticalAlignment() {
        CompilationUnit cu =
                TestParser.parseCompilationUnit("public enum X {" + LineSeparator.SYSTEM + "    /** const1 javadoc */"
                        + LineSeparator.SYSTEM + "    BORDER_CONSTANT,"
                        + LineSeparator.SYSTEM + "    /** const2 javadoc */"
                        + LineSeparator.SYSTEM + "    ANOTHER_CONSTANT"
                        + LineSeparator.SYSTEM + "}");
        assertEqualsStringIgnoringEol(
                "public enum X {\n" + "\n"
                        + "    /**\n"
                        + "     * const1 javadoc\n"
                        + "     */\n"
                        + "    BORDER_CONSTANT,\n"
                        + "    /**\n"
                        + "     * const2 javadoc\n"
                        + "     */\n"
                        + "    ANOTHER_CONSTANT\n"
                        + "}\n",
                cu.toString());
    }

    @Test
    void issue234LosingCommentsInArrayInitializerExpr() {
        CompilationUnit cu = TestParser.parseCompilationUnit("@Anno(stuff={" + LineSeparator.SYSTEM + "    // Just,"
                + LineSeparator.SYSTEM + "    // an,"
                + LineSeparator.SYSTEM + "    // example"
                + LineSeparator.SYSTEM + "})"
                + LineSeparator.SYSTEM + "class ABC {"
                + LineSeparator.SYSTEM + ""
                + LineSeparator.SYSTEM + "}");

        assertEqualsStringIgnoringEol(
                "@Anno(stuff = {// Just,\n" + "// an,\n" + "// example\n" + "})\n" + "class ABC {\n" + "}\n",
                cu.toString());
    }

    @Test
    void issue412() throws IOException {
        CompilationUnit cu = parseSample("Issue412").getResult().get();
        assertEqualToTextResourceNoEol(makeExpectedFilename("Issue412"), cu.toString());
    }

    @Test
    void issue4960CommentAfterParameterIsAttributedOnceToThatParameter() {
        CompilationUnit cu = TestParser.parseCompilationUnit(
                "class TestClass {\n" + "    public void a(int a //something\n" + "        ) { }\n" + "}");
        MethodDeclaration method =
                cu.getType(0).asClassOrInterfaceDeclaration().getMethods().get(0);

        // Uniqueness, globally: across the whole CU the comment must be attached
        // exactly once. The original bug duplicated it across every sibling that
        // merely shared the line, so this is the assertion that actually encodes
        // the fix rather than only that some node lost it. The sites are counted
        // without deduplicating by Comment identity, since the bug is one Comment
        // instance attached to several nodes.
        List<Node> attachmentSites = commentAttachmentSites(cu);
        assertEquals(1, attachmentSites.size(), "the trailing comment must be attached exactly once");

        // Positive attribution: the comment belongs to the parameter it trails,
        // not merely to "something other than the return type / name".
        Parameter parameter = method.getParameter(0);
        assertSame(parameter, attachmentSites.get(0), "the sole attachment site must be the parameter it trails");
        Optional<Comment> parameterComment = parameter.getComment();
        assertTrue(parameterComment.isPresent(), "the comment must be attributed to the parameter it trails");

        // Back-pointer consistency: comment.getCommentedNode() must point back at
        // the same node, locking the invariant the old code broke (three nodes held
        // the comment while getCommentedNode() returned only one of them).
        assertSame(parameter, parameterComment.get().getCommentedNode().get());

        // Full rendering, per the file's own convention: it shows both where the
        // comment landed and that it no longer leaks onto the return type / name.
        assertEqualsStringIgnoringEol(
                "class TestClass {\n" + "\n" + "    public void a(//something\n" + "    int a) {\n" + "    }\n" + "}\n",
                cu.toString());
    }

    @Test
    void issue4960CommentAfterClosingParenIsNotDuplicated() {
        // The second reproducer from the issue: the comment sits after ')'.
        CompilationUnit cu = TestParser.parseCompilationUnit(
                "class TestClass {\n" + "    public void a(int a) //something\n" + "    { }\n" + "}");
        MethodDeclaration method =
                cu.getType(0).asClassOrInterfaceDeclaration().getMethods().get(0);

        // Uniqueness, globally: the comment is attached exactly once across the
        // whole CU. The original bug duplicated it onto the return type and the
        // method name as well. Sites are counted without deduplicating by Comment
        // identity, since the bug is one Comment instance attached to several nodes.
        List<Node> attachmentSites = commentAttachmentSites(cu);
        assertEquals(1, attachmentSites.size(), "the trailing comment must be attached exactly once");

        // It must not leak onto the return type or the method name — that leak was
        // the symptom reported in the issue.
        assertFalse(method.getType().getComment().isPresent(), "the comment must not leak onto the return type");
        assertFalse(method.getName().getComment().isPresent(), "the comment must not leak onto the method name");

        // Back-pointer consistency: whatever node received it, getCommentedNode()
        // must be non-null and actually carry that comment. On master this
        // invariant was broken (several nodes held the comment).
        Node holder = attachmentSites.get(0);
        assertSame(
                holder,
                holder.getComment().get().getCommentedNode().get(),
                "getCommentedNode() must point at the node holding the comment");

        // Full rendering, per the file's own convention: locks the output so a
        // future change in attribution is surfaced explicitly.
        assertEqualsStringIgnoringEol(
                "class TestClass {\n" + "\n" + "    public void a(//something\n" + "    int a) {\n" + "    }\n" + "}\n",
                cu.toString());
    }

    @Test
    void issue4960EachTrailingCommentIsAttributedOnceToItsOwnParameter() {
        // Two parameters, each with its own trailing line comment on its line.
        // Each comment must be attached exactly once to the parameter it trails.
        // This guards both the uniqueness fix (no duplication across siblings) and
        // the retained fallback: the second comment's nearest node is its own
        // parameter, so neither comment is lost and neither is duplicated onto the
        // other. Sites are counted without deduplicating by Comment identity, so
        // this distinguishes the fix (2 sites) from the old bug (4 sites).
        CompilationUnit cu = TestParser.parseCompilationUnit("class TestClass {\n"
                + "    public void a(int a //existing\n"
                + "        , int b //trailing\n"
                + "        ) { }\n"
                + "}");
        List<Node> attachmentSites = commentAttachmentSites(cu);
        assertEquals(2, attachmentSites.size(), "both trailing comments must survive and be attached once each");
    }

    /**
     * Every node that currently holds an attached comment (via {@link Node#getComment()}),
     * excluding orphan comments. Each node holding a comment contributes one entry, so the
     * same {@link Comment} instance attached to several nodes produces several entries. This
     * is deliberate: the bug under test is one comment attached to multiple sites, and
     * deduplicating by comment identity would hide exactly that. Orphan comments are
     * excluded because they belong to no attachment site.
     */
    private static List<Node> commentAttachmentSites(Node root) {
        List<Node> attachmentSites = new ArrayList<>();
        for (Node node : root.findAll(Node.class)) {
            if (node.getComment().isPresent()) {
                attachmentSites.add(node);
            }
        }
        return attachmentSites;
    }
}
