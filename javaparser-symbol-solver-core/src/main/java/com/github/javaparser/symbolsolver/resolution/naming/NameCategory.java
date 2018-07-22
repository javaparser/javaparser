package com.github.javaparser.symbolsolver.resolution.naming;

/**
 * Context causes a name syntactically to fall into one of seven categories: ModuleName, PackageName, TypeName,
 * ExpressionName, MethodName, PackageOrTypeName, or AmbiguousName.
 * TypeName is less expressive than the other six categories, because it is denoted with TypeIdentifier, which excludes
 * the character sequence var (§3.8).
 *
 * See JLS 6.5 (https://docs.oracle.com/javase/specs/jls/se10/html/jls-6.html#jls-6.5)
 */
public enum NameCategory {
    MODULE_NAME,
    PACKAGE_NAME,
    TYPE_NAME,
    EXPRESSION_NAME,
    METHOD_NAME,
    PACKAGE_OR_TYPE_NAME,
    AMBIGUOUS_NAME;

    public boolean isNameAcceptable(String name) {
        if (this == TYPE_NAME && name.equals("var")) {
            return false;
        } else {
            return true;
        }
    }
}
