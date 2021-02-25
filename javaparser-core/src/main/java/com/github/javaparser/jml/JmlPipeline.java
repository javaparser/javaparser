package com.github.javaparser.jml;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.jml.services.*;
import lombok.var;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (1/30/20)
 */
public class JmlPipeline {
    private final Lookup lookup;

    public JmlPipeline() {
        this(new Lookup(JmlFacade.defaultServices));
    }

    public JmlPipeline(Lookup lookup) {
        this.lookup = lookup;
    }

    public void processJml(CompilationUnit ast) {
        var detection = lookup.get(IJmlDetection.class);
        var jmlComments = new LinkedList<Comment>();
        for (Comment c : ast.getAllContainedComments()) {
            var str = c.getContent();
            if (detection.isJmlComment(str)) {
                jmlComments.add(c);
            }
        }

        //TODO Maybe repacking the consecutive jml comments into one comment.
        //    jmlComments = detection.repack(jmlComments);

        var parser = lookup.get(IJmlParser.class);
        var attacher = lookup.get(IJmlAttacher.class);
        for (Comment comment : jmlComments) {
            List<Jmlish> jmlNodes = parser.create(comment);
            attacher.attach(ast, jmlNodes);
        }
        lookup.lookupAll(IJmlAnnotationProcessor.class).forEach(it -> it.process(ast));
    }

    public Lookup getLookup() {
        return lookup;
    }
}