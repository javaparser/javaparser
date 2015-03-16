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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.lexical.Comment;
import com.github.javaparser.ast.lexical.CommentAttributes;
import com.github.javaparser.utils.TestResources;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import java.io.IOException;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * @author Didier Villevalois
 */
@RunWith(JUnit4.class)
public class CommentsTest {

    private final Pattern commentPattern = Pattern.compile("([a-zA-Z]+)\\(([0-9])\\) \\[([^\\]]*)\\]");

    private TestResources resources = new TestResources("com/github/javaparser/comments/", "");

    @Test
    public void checkAllComments() throws ParseException, IOException {
        CompilationUnit cu = parse("AllComments.java", null, true, true);
        checkComments(cu, 29);
    }

    private void checkComments(CompilationUnit cu, int expectedTotal) {
        Assert.assertEquals("Total comment count", expectedTotal, checkCommentsIn(cu, ""));
    }

    private int checkCommentsIn(Node node, String path) {
        int totalComments = 0;

        CommentAttributes comments = node.getCommentAttributes();
        if (comments != null) {
            totalComments += checkComments(comments.getLeadingComments(), "Leading", path);
            totalComments += checkComments(comments.getDanglingComments(), "Dangling", path);
            totalComments += checkComment(comments.getTrailingComment(), "Trailing", 0, path);
        }

        List<Node> children = node.getChildrenNodes();
        totalComments += checkCommentsIn(children, path);

        return totalComments;
    }

    private int checkCommentsIn(List<Node> children, String path) {
        int totalComments = 0;
        for (int i = 0; i < children.size(); i++) {
            Node child = children.get(i);
            String childPath = path.isEmpty() ? path + i : path + "." + i;
            totalComments += checkCommentsIn(child, childPath);
        }
        return totalComments;
    }

    private int checkComments(List<Comment> comments, String type, String path) {
        if (comments == null) return 0;

        int totalComments = 0;
        for (int i = 0; i < comments.size(); i++) {
            Comment comment = comments.get(i);
            totalComments += checkComment(comment, type, i, path);
        }
        return totalComments;
    }

    private int checkComment(Comment comment, String type, int i, String path) {
        if (comment == null) return 0;

        String image = comment.image();
        if (image.startsWith("/**")) {
            image = image.substring(4, image.length() - 3);
        } else if (image.startsWith("/*")) {
            image = image.substring(3, image.length() - 3);
        } else if (image.startsWith("//")) {
            image = image.substring(3);
        }

        Matcher matcher = commentPattern.matcher(image);

        Assert.assertTrue(matcher.matches());
        String commentType = matcher.group(1);
        int commentIndex = Integer.parseInt(matcher.group(2));
        String commentPath = matcher.group(3);

        Assert.assertEquals("Comment '" + image + "' is " + type, type, commentType);
        Assert.assertEquals("Comment '" + image + "' has index " + i, i, commentIndex);
        Assert.assertEquals("Comment '" + image + "' is at path " + path, path, commentPath);
        return 1;
    }

    private CompilationUnit parse(String path, String encoding, boolean attributeComments, boolean preserveLexemes)
            throws ParseException, IOException {
        return JavaParser.parse(resources.getResourceAsStream(path), encoding, attributeComments, preserveLexemes);
    }
}
