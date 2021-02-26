package com.github.javaparser.jml;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.utils.Pair;
import org.jetbrains.annotations.NotNull;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.logging.Handler;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (1/30/20)
 */
public class JmlPipeline {
    public void processJml(CompilationUnit ast) {
        var jmlComments =
                ast.getAllContainedComments().stream()
                        .filter(this::isJmlComment)
                        .collect(Collectors.toList());

        //TODO Maybe repacking the consecutive jml comments into one comment.
        //    jmlComments = detection.repack(jmlComments);

        for (Comment comment : jmlComments) {
            List<Pair<Jmlish, Handler>> jmlNodes = parseComment(comment);
            for (Pair<Jmlish, Handler> pair : jmlNodes) {
                //pair.b.attach
            }
        }
        processAnnotationsJml(ast);
    }

    /**
     * Processing of the given compilation unit.
     * This method should find appropriate annotation
     * inside the given {@ast} and translate them into
     * JML specification.
     *
     * @param ast
     */
    protected void processAnnotationsJml(CompilationUnit ast) {
    }

    /**
     * Parses the String content into a parse tree.
     * <p>
     * The parse tree is after execution set {@link JmlComment#setContext}.
     * Problems found during parsing should be reported to {@link JmlComment#getParserErrors()}
     *
     * @param comment a jml comment
     */
    private List<Pair<Jmlish, Handler>> parseComment(Comment comment) {
        return null;
    }

    private static final Pattern JML_COMMENT_PATTERN
            = Pattern.compile("^\\s*(//|/[*])(([-+]\\w+)*)[@].*", Pattern.DOTALL);

    public boolean isJmlComment(@NotNull Comment comment) {
        return getAnnotationKeys(comment.getContent()) != null;
    }

    /**
     * @param comment
     * @return null if the given comment is non-jml, else a set with the annotation keys are returned.
     */
    public Set<String> getAnnotationKeys(@NotNull String comment) {
        var m = JML_COMMENT_PATTERN.matcher(comment);
        if (m.matches()) {
            if (m.groupCount() >= 3 && !m.group(2).trim().isEmpty()) {
                Set<String> s = new TreeSet<>();
                var annotations = m.group(2);
                Pattern.compile("(?=[+-])").splitAsStream(annotations)
                        .filter(it -> !it.trim().isEmpty())
                        .forEach(s::add);
                return s;
            }
            return Collections.emptySet();
        }
        return null;
    }
}