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

package com.github.javaparser.parser;

import com.github.javaparser.Position;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ModifierSet;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;

import java.io.InputStream;
import java.io.Reader;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Didier Villevalois
 */
public abstract class Parser {

    boolean preserveLexemes;

    public static Parser newInstance(InputStream in, String encoding, boolean preserveLexemes) {
        ASTParser parser = new ASTParser(in, encoding);
        parser.preserveLexemes = preserveLexemes;
        return parser;
    }

    public static Parser newInstance(Reader in, boolean preserveLexemes) {
        ASTParser parser = new ASTParser(in);
        parser.preserveLexemes = preserveLexemes;
        return parser;
    }

    public abstract void reset(InputStream in, String encoding);

    public abstract void reset(Reader in);

    public abstract CompilationUnit CompilationUnit() throws ParseException;

    public abstract ImportDeclaration ImportDeclaration() throws ParseException;

    public abstract BodyDeclaration AnnotationBodyDeclaration() throws ParseException;

    public abstract BlockStmt Block() throws ParseException;

    public abstract Statement Statement() throws ParseException;

    public abstract Expression Expression() throws ParseException;

    public abstract AnnotationExpr Annotation() throws ParseException;


    protected List add(List list, Object obj) {
        if (list == null) {
            list = new LinkedList();
        }
        list.add(obj);
        return list;
    }

    protected List add(int pos, List list, Object obj) {
        if (list == null) {
            list = new LinkedList();
        }
        list.add(pos, obj);
        return list;
    }

    protected class ModifiersAndAnnotations {

        public final Lexeme first;
        private int modifiers;
        private List annotations;

        public ModifiersAndAnnotations(Lexeme first) {
            this.first = first;
        }

        void addModifier(int mod, Token token) throws ParseException {
            if ((ModifierSet.hasModifier(modifiers, mod))) {
                // TODO We should not stop the parsing for such an error
                // This defeats the purpose of recognizing all mods in one production
                throwParseException(token, "Duplicated modifier");
            }
            modifiers = ModifierSet.addModifier(modifiers, mod);
        }

        void addAnnotation(AnnotationExpr annotation) {
            if (annotations == null) {
                annotations = new LinkedList();
            }
            annotations.add(annotation);
        }

        public List annotations() {
            return annotations;
        }

        public int modifiers() {
            return modifiers;
        }
    }

    protected ModifiersAndAnnotations newModifiersAndAnnotations() {
        return new ModifiersAndAnnotations(next());
    }

    protected int addModifier(int modifiers, int mod, Token token) throws ParseException {
        if ((ModifierSet.hasModifier(modifiers, mod))) {
            throwParseException(token, "Duplicated modifier");
        }
        return ModifierSet.addModifier(modifiers, mod);
    }

    protected abstract void throwParseException(Token token, String message) throws ParseException;

    void postProcessToken(Token token) {
        if (!preserveLexemes) return;
        lastLexeme = buildLexemeChain(token);
    }

    private Lexeme lastLexeme;

    private Lexeme buildLexemeChain(Token token) {
        Lexeme current = TokenLexemeConversion.instantiate(token.kind, token.image);
        token.lexeme = current;

        current.setBegin(new Position(token.beginLine, token.beginColumn));
        current.setEnd(new Position(token.endLine, token.endColumn));

        Lexeme previous;
        if (token.specialToken != null) {
            previous = buildLexemeChain(token.specialToken);
        } else {
            previous = lastLexeme;
        }

        current.setPrevious(previous);
        if (previous != null) previous.setNext(current);

        return current;
    }

    protected abstract Token getToken(int index);

    protected Lexeme next() {
        if (!preserveLexemes) return null;
        return getToken(1).lexeme;
    }

    protected Lexeme previous() {
        if (!preserveLexemes) return null;
        return getToken(0).lexeme;
    }
}
