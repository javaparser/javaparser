/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 21/11/2006
 */
package japa.parser.ast.body;

import japa.parser.ast.DocumentableNode;
import japa.parser.ast.comments.JavadocComment;
import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class AnnotationDeclaration extends TypeDeclaration implements DocumentableNode {
    @Override
    public void setJavaDoc(JavadocComment javadocComment) {
        //To change body of implemented methods use File | Settings | File Templates.
    }

    public AnnotationDeclaration() {
    }

    public AnnotationDeclaration(int modifiers, String name) {
        super(modifiers, name);
    }

    public AnnotationDeclaration(int modifiers, List<AnnotationExpr> annotations, String name, List<BodyDeclaration> members) {
        super(annotations, modifiers, name, members);
    }

    public AnnotationDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers, List<AnnotationExpr> annotations, String name, List<BodyDeclaration> members) {
        super(beginLine, beginColumn, endLine, endColumn, annotations, modifiers, name, members);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Override
    public JavadocComment getJavaDoc() {
        return null;  //To change body of implemented methods use File | Settings | File Templates.
    }
}
