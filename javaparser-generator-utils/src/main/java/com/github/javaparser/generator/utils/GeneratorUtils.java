package com.github.javaparser.generator.utils;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;

public final class GeneratorUtils {
    private GeneratorUtils() {
    }

    /**
     * Capitalizes the first character in the string.
     */
    public static String capitalize(String original) {
        if (original.isEmpty()) {
            return original;
        }
        return original.substring(0, 1).toUpperCase() + original.substring(1);
    }

    /**
     * Lower-cases the first character in the string.
     */
    public static String decapitalize(String string) {
        if (string.isEmpty()) {
            return string;
        }
        return string.substring(0, 1).toLowerCase() + string.substring(1);
    }

    public static String getterName(Class<?> type, String name) {
        if (name.startsWith("is")) {
            return name;
        } else if (type.equals(Boolean.class)) {
            return "is" + capitalize(name);
        }
        return "get" + capitalize(name);
    }

    public static String setterName(String fieldName) {
        if (fieldName.startsWith("is")) {
            return "set" + fieldName.substring(2);
        }
        return "set" + capitalize(fieldName);
    }

    public static String optionalOf(String text, boolean isOptional) {
        if (isOptional) {
            return f("Optional.of(%s)", text);
        } else {
            return "Optional.empty()";
        }
    }

    /**
     * A shortcut to String.format.
     */
    public static String f(String format, Object... params) {
        return String.format(format, params);
    }

    /**
     * Calculates the path to a file in a package.
     *
     * @param root the root directory in which the package resides
     * @param pkg the package in which the file resides, like "com.laamella.parser"
     * @param file the filename of the file in the package.
     */
    public static Path fileInPackageAbsolutePath(String root, String pkg, String file) {
        pkg = packageToPath(pkg);
        return Paths.get(root, pkg, file).normalize();
    }

    public static Path fileInPackageAbsolutePath(Path root, String pkg, String file) {
        return fileInPackageAbsolutePath(root.toString(), pkg, file);
    }

    /**
     * Turns a package and a file into a relative path. "com.laamella" and "Simple.java" will become
     * "com/laamella/Simple.java"
     */
    public static Path fileInPackageRelativePath(String pkg, String file) {
        pkg = packageToPath(pkg);
        return Paths.get(pkg, file).normalize();
    }

    /**
     * Converts a package name like "com.laamella.parser" to a path like "com/laamella/parser"
     */
    public static String packageToPath(String pkg) {
        return pkg.replace(".", File.separator);
    }

    /**
     * Calculates the path of a package.
     *
     * @param root the root directory in which the package resides
     * @param pkg the package, like "com.laamella.parser"
     */
    public static Path packageAbsolutePath(String root, String pkg) {
        pkg = packageToPath(pkg);
        return Paths.get(root, pkg).normalize();
    }

    public static Path packageAbsolutePath(Path root, String pkg) {
        return packageAbsolutePath(root.toString(), pkg);
    }

    /**
     * For generators that are inside the JavaParser project, this will get the root path of the project.
     */
    public static Path getJavaParserBasePath() {
        String path = GeneratorUtils.class.getProtectionDomain().getCodeSource().getLocation().getPath();
        // Silly Windows fix
        if (path.charAt(2) == ':') {
            path = path.substring(1);
        }
        return Paths.get(path, "..", "..", "..");
    }

    /**
     * @param input "aCamelCaseString"
     * @return "A_CAMEL_CASE_STRING"
     */
    public static String camelCaseToScreaming(String input) {
        if (input.isEmpty()) {
            return "";
        }
        StringBuilder scream = new StringBuilder(input.substring(0, 1).toUpperCase());
        for (char c : input.substring(1).toCharArray()) {
            if (Character.isUpperCase(c)) {
                scream.append("_");
            }
            scream.append(Character.toUpperCase(c));
        }
        return scream.toString();
    }

}
