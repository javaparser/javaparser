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

package com.github.javaparser.ast.lexical;

/**
 * @author Didier Villevalois
 */
public enum KeywordKind {
    ABSTRACT("abstract"),
    ASSERT("assert"),
    BOOLEAN("boolean"),
    BREAK("break"),
    BYTE("byte"),
    CASE("case"),
    CATCH("catch"),
    CHAR("char"),
    CLASS("class"),
    CONST("const"),
    CONTINUE("continue"),
    DEFAULT("default"),
    DO("do"),
    DOUBLE("double"),
    ELSE("else"),
    ENUM("enum"),
    EXTENDS("extends"),
    FALSE("false"),
    FINAL("final"),
    FINALLY("finally"),
    FLOAT("float"),
    FOR("for"),
    GOTO("goto"),
    IF("if"),
    IMPLEMENTS("implements"),
    IMPORT("import"),
    INSTANCEOF("instanceof"),
    INT("int"),
    INTERFACE("interface"),
    LONG("long"),
    NATIVE("native"),
    NEW("new"),
    NULL("null"),
    PACKAGE("package"),
    PRIVATE("private"),
    PROTECTED("protected"),
    PUBLIC("public"),
    RETURN("return"),
    SHORT("short"),
    STATIC("static"),
    STRICTFP("strictfp"),
    SUPER("super"),
    SWITCH("switch"),
    SYNCHRONIZED("synchronized"),
    THIS("this"),
    THROW("throw"),
    THROWS("throws"),
    TRANSIENT("transient"),
    TRUE("true"),
    TRY("try"),
    VOID("void"),
    VOLATILE("volatile"),
    WHILE("while"),
    // Keep the last comma
    ;

    public final String image;

    KeywordKind(String image) {
        this.image = image;
    }
}
