package com.github.javaparser.parser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ModifierSet;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
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

    public static Parser newInstance(InputStream in, String encoding) {
        return new ASTParser(in, encoding);
    }

    public static Parser newInstance(Reader in) {
        return new ASTParser(in);
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

    protected class Modifier {

        final int modifiers;
        final List annotations;
        final int beginLine;
        final int beginColumn;

        public Modifier(int beginLine, int beginColumn, int modifiers, List annotations) {
            this.beginLine = beginLine;
            this.beginColumn = beginColumn;
            this.modifiers = modifiers;
            this.annotations = annotations;
        }
    }

    public int addModifier(int modifiers, int mod, Token token) throws ParseException {
        if ((ModifierSet.hasModifier(modifiers, mod))) {
            throwParseException(token, "Duplicated modifier");
        }
        return ModifierSet.addModifier(modifiers, mod);
    }

    protected abstract void throwParseException(Token token, String message) throws ParseException;
}
