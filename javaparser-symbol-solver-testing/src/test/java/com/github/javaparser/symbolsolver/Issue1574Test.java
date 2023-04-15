/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.Comment;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

public class Issue1574Test {
    private static final String LINE_FILE = "src/test/resources/issue1574/Comment.java";
    private static final String BLOCK_FILE = "src/test/resources/issue1574/BlockComment.java";
    private static final String ORPHAN_FILE = "src/test/resources/issue1574/ClassWithOrphanComments.java";
    @Test
    void removeAllCommentsBeforePackageLine() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(LINE_FILE));
        for(Comment child: cu.getComments()){
            child.remove();
        }
        assertEquals(0,cu.getComments().size());
        assertFalse(cu.getComment().isPresent());
    }
    @Test
    void removeAllCommentsBeforePackageBlock() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(BLOCK_FILE));
        for(Comment child: cu.getComments()){
            child.remove();
        }
        assertEquals(0,cu.getComments().size());
        assertFalse(cu.getComment().isPresent());
    }
    @Test
    void getAllContainedCommentBeforePackageDeclarationLine() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(LINE_FILE));
        List<Comment> comments = cu.getAllContainedComments();
        assertEquals(2,comments.size());

    }
    @Test
    void getAllContainedCommentBeforePackageDeclarationBlock() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(BLOCK_FILE));
        List<Comment> comments = cu.getAllContainedComments();
        assertEquals(2,comments.size());

    }
    @Test
    void getAllCommentBeforePackageDeclarationOrphan() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(ORPHAN_FILE));
        List<Comment> comments = cu.getAllContainedComments();
        assertEquals(6,comments.size());

    }
    @Test
    void getOrphanComments() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(LINE_FILE));
        List<Comment> comments = cu.getOrphanComments();
        //The 2 first should be orphan comment while the third will be associated to the package
        assertEquals(1,comments.size());


    }
    @Test
    void getOrphanCommentsBlock() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(BLOCK_FILE));
        List<Comment> comments = cu.getOrphanComments();
        //The 2 first should be orphan comment while the third will be associated to the package
        assertEquals(1,comments.size());

    }
    @Test
    void getAllCommentBeforePackageDeclarationLine() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(LINE_FILE));
        List<Comment> comments = cu.getComments();
        assertEquals(3,comments.size());

    }
    @Test
    void getAllCommentBeforePackageDeclarationBlock() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(BLOCK_FILE));
        List<Comment> comments = cu.getComments();
        assertEquals(3,comments.size());
    }

}
