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
 * Created on 05/10/2006
 */
package japa.parser.ast.body;

import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.type.Type;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class FieldDeclaration extends BodyDeclaration {

    private int modifiers;

    private Type type;

    private List<VariableDeclarator> variables;

    public FieldDeclaration() {
    }

    public FieldDeclaration(int modifiers, Type type, VariableDeclarator variable) {
    	setModifiers(modifiers);
    	setType(type);
    	List<VariableDeclarator> aux = new ArrayList<VariableDeclarator>();
    	aux.add(variable);
    	setVariables(aux);
    }

    public FieldDeclaration(int modifiers, Type type, List<VariableDeclarator> variables) {
    	setModifiers(modifiers);
    	setType(type);
    	setVariables(variables);
    }

    public FieldDeclaration(JavadocComment javaDoc, int modifiers, List<AnnotationExpr> annotations, Type type, List<VariableDeclarator> variables) {
        super(annotations, javaDoc);
        setModifiers(modifiers);
    	setType(type);
    	setVariables(variables);
    }

    public FieldDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, JavadocComment javaDoc, int modifiers, List<AnnotationExpr> annotations, Type type, List<VariableDeclarator> variables) {
        super(beginLine, beginColumn, endLine, endColumn, annotations, javaDoc);
        setModifiers(modifiers);
    	setType(type);
    	setVariables(variables);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    /**
     * Return the modifiers of this member declaration.
     * 
     * @see ModifierSet
     * @return modifiers
     */
    public int getModifiers() {
        return modifiers;
    }

    public Type getType() {
        return type;
    }

    public List<VariableDeclarator> getVariables() {
        return variables;
    }

    public void setModifiers(int modifiers) {
        this.modifiers = modifiers;
    }

    public void setType(Type type) {
        this.type = type;
		setAsParentNodeOf(this.type);
    }

    public void setVariables(List<VariableDeclarator> variables) {
        this.variables = variables;
		setAsParentNodeOf(this.variables);
    }
}
