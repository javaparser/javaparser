package com.github.javaparser.jml.services;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Jmlish;
import jml.JmlComment;
import org.jetbrains.annotations.NotNull;

import java.util.Collection;

/**
 * A service associates {@link JmlComment}s to their appropiate ASTNode
 *
 * @author Alexander Weigl
 * @version 1 (1/31/20)
 */
public interface IJmlAttacher {
    /**
     * This method should attach the {@code jmlComments}
     * to the appropriate {@link ASTNode} in {@code ast}.
     *
     * @param ast         the ast, in which the comments where found
     * @param jmlComments a list of jml comments
     * @see jml.ASTProperties#attachJmlComment(ASTNode, JmlComment)
     */
    void attach(@NotNull CompilationUnit ast,
                @NotNull Collection<Jmlish> jmlComments);

    void setAttachmentHandler(int type, Handler handler);

    public interface Handler {
        void attach(JmlComment c, @NotNull CompilationUnit ast);
    }
}
