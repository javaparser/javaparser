package com.github.javaparser.ast.body;

import java.util.EnumSet;

import com.github.javaparser.ast.AccessSpecifier;

public enum Modifier {
	PUBLIC("public"),
	PRIVATE("private"),
	PROTECTED("protected"),
	STATIC("static"),
	FINAL("final"),
	SYNCHRONIZED("synchronized"),
	VOLATILE("volatile"),
	TRANSIENT("transient"),
	NATIVE("native"),
	ABSTRACT("abstract"),
	STRICTFP("strictfp");

    String lib;

    private Modifier(String lib) {
        this.lib = lib;
    }

    /**
     * @return the lib
     */
    public String getLib() {
        return lib;
    }

    public static AccessSpecifier getAccessSpecifier(EnumSet<Modifier> modifiers) {
        if (modifiers.contains(Modifier.PUBLIC)) {
            return AccessSpecifier.PUBLIC;
        } else if (modifiers.contains(Modifier.PROTECTED)) {
            return AccessSpecifier.PROTECTED;
        } else if (modifiers.contains(Modifier.PRIVATE)) {
            return AccessSpecifier.PRIVATE;
        } else {
            return AccessSpecifier.DEFAULT;
        }
    }
}
