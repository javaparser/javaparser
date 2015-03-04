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
        lastLexeme = buildLexemeChain(token, null);
        if (firstLexeme == null) firstLexeme = lastLexeme;
    }

    private Lexeme firstLexeme;
    private Lexeme lastLexeme;

    private Lexeme buildLexemeChain(Token token, Lexeme next) {
        Lexeme current = TokenLexemeConversion.instantiate(token.kind, token.image);
        token.lexeme = current;

        current.setBegin(new Position(token.beginLine, token.beginColumn));
        current.setEnd(new Position(token.endLine, token.endColumn));

        Lexeme previous;
        if (token.specialToken != null) {
            previous = buildLexemeChain(token.specialToken, current);
        } else {
            previous = lastLexeme;
        }

        current.setPrevious(previous);
        if (previous != null) previous.setNext(current);

        return current;
    }

    protected abstract Token getToken(int index);

    protected Lexeme next() {
        return getToken(1).lexeme;
    }

    protected Lexeme previous() {
        return getToken(0).lexeme;
    }
}
