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

package com.github.javaparser.full.utils;

import java.io.File;
import java.io.IOException;
import java.net.URLDecoder;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.regex.Pattern;

/**
 * This code has been inspired from code of Greg Briggs as found http://www.uofr.net/~greg/java/get-resource-listing.html.
 *
 * @author Federico Tomassetti
 * @author Didier Villevalois
 */
public class ResourceHelper {

    private Set<Pattern> classpathsToAvoids = new HashSet<Pattern>();

    public ResourceHelper() {
    }

    /**
     * This resorce helper is based on the current classpath but excluded jars from the jre.
     */
    public static ResourceHelper classpathExcludingJre() {
        ResourceHelper resourceHelper = new ResourceHelper();
        resourceHelper.ignore(Pattern.compile(".*/jre/.*"));
        return resourceHelper;
    }

    /**
     * Instruct to ignore all the classpath elements which corresponds to the given regular expression.
     */
    public void ignore(Pattern regex) {
        classpathsToAvoids.add(regex);
    }

    public Set<String> listDirectories(String path) throws IOException {
        return list(path, new DirectoryNameMapper(path));
    }

    interface Mapper<E> {

        E mapFile(String path, File element);

        E mapJarEntry(String path, JarFile jarFile, JarEntry jarEntry);
    }

    private <E> Set<E> list(String packageName, Mapper<E> mapper) throws IOException {
        Set<E> elements = new LinkedHashSet<E>();
        for (String classpathElement : System.getProperty("java.class.path").split(":")) {
            boolean skip = false;
            for (Pattern classpathToAvoid : classpathsToAvoids) {
                if (classpathToAvoid.matcher(classpathElement).matches()) {
                    skip = true;
                }
            }
            if (skip) {
                continue;
            }

            if (classpathElement.endsWith(".jar")) {
                elements.addAll(exploreJar(classpathElement, packageName, mapper));
            } else {
                File f = new File(classpathElement);
                if (f.isDirectory()) {
                    elements.addAll(exploreDir(f, packageName, mapper));
                }
            }
        }
        return elements;
    }

    class DirectoryNameMapper implements Mapper<String> {

        private final String basePath;

        public DirectoryNameMapper(String basePath) {
            this.basePath = basePath;
        }

        @Override
        public String mapFile(String path, File element) {
            return stripPath(path);
        }

        @Override
        public String mapJarEntry(String path, JarFile jarFile, JarEntry jarEntry) {
            return stripPath(jarEntry.getName());
        }

        private String stripPath(String path) {
            String subPath = path.substring(basePath.length());
            int slashIndex = subPath.indexOf('/');
            subPath = slashIndex == -1 ? subPath : subPath.substring(0, slashIndex);
            return subPath;
        }
    }

    private <E> Set<E> exploreJar(String jarPath, String path, Mapper<E> mapper) throws IOException {
        JarFile jar = new JarFile(URLDecoder.decode(jarPath, "UTF-8"));
        Enumeration<JarEntry> entries = jar.entries(); //gives ALL entries in jar
        Set<E> result = new LinkedHashSet<E>(); //ignore duplicates in case it is a subdirectory
        while (entries.hasMoreElements()) {
            JarEntry jarEntry = entries.nextElement();
            String name = jarEntry.getName();
            if (name.startsWith(path)) { //filter according to the path
                String entry = name.substring(path.length());
                int checkSubdir = entry.indexOf("/");
                if (checkSubdir >= 0) {
                    // if it is a subdirectory, we just return the directory name
                    entry = entry.substring(0, checkSubdir);
                }
                result.add(mapper.mapJarEntry(entry, jar, jarEntry));
            }
        }
        return result;
    }

    private <E> Set<E> exploreDir(File dir, String path, Mapper<E> mapper) throws IOException {
        Set<E> set = new LinkedHashSet<E>();
        exploreDir(dir, path, "", set, mapper);
        return set;
    }

    private <E> void exploreDir(File dir, String path, String base, Set<E> collector, Mapper<E> mapper) throws IOException {
        for (File child : dir.listFiles()) {
            String nextBase = base.isEmpty() ? child.getName() : base + "/" + child.getName();
            if (child.isFile()) {
                if (nextBase.startsWith(path)) {
                    collector.add(mapper.mapFile(nextBase, child));
                }
            } else if (child.isDirectory()) {
                exploreDir(child, path, nextBase, collector, mapper);
            }
        }
    }
}
