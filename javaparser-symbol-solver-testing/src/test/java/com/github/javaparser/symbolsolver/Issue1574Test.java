package com.github.javaparser.symbolsolver;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.Comment;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue1574Test {
    private static final String FILE_PATH = "src/test/resources/issue1574/Comment.java";
    @Test
    void getAllCommentBeforePackageDeclaration() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(FILE_PATH));
        List<Comment> comments = cu.getAllContainedComments();
        assertEquals(3,comments.size());

    }
    @Test
    void geOrphanComments() throws Exception{
        CompilationUnit cu = StaticJavaParser.parse(new File(FILE_PATH));
        List<Comment> comments = cu.getOrphanComments();
        //The 2 first should be orphan comment while the third will be associated to the package
        assertEquals(2,comments.size());

    }
}
