package com.github.javaparser.generator.utils;

import java.io.File;
import java.lang.reflect.Field;
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
    public static Path fileInPackagePath(String root, String pkg, String file) {
        pkg = packageToPath(pkg);
        return Paths.get(root, pkg, file).normalize();
    }

    public static Path fileInPackagePath(Path root, String pkg, String file) {
        return fileInPackagePath(root.toString(), pkg, file);
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
    public static Path packagePath(String root, String pkg) {
        pkg = packageToPath(pkg);
        return Paths.get(root, pkg).normalize();
    }

    public static Path packagePath(Path root, String pkg) {
        return packagePath(root.toString(), pkg);
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


}
