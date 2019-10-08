/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.generator.core.other;

import com.github.javaparser.generator.Generator;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.io.*;
import java.util.*;

/**
 * Generates the bnd.bnd file in javaparser-core.
 */
public class BndGenerator extends Generator {

    private final Set<String> packages = new HashSet<>();

    public BndGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    public void generate() throws IOException {
        Log.info("Running %s", () -> getClass().getSimpleName());
        File root = sourceRoot.getRoot().toFile();
        visit(root, "");
        List<String> sortedPackages = new ArrayList<>(packages);
        sortedPackages.sort(String::compareTo);
        File projectRoot = root.getParentFile().getParentFile().getParentFile();
        File template = new File(projectRoot, "bnd.bnd.template");
        File output = new File(projectRoot, "bnd.bnd");
        String lineSeparator = System.getProperty("line.separator");
        StringBuilder packagesList = new StringBuilder("\\" + lineSeparator);
        boolean first = true;
        for(String pkg : sortedPackages) {
            if(!first) {
                packagesList.append(", \\").append(lineSeparator);
            }
            packagesList.append("    ").append(pkg);
            first = false;
        }
        try(BufferedReader reader = new BufferedReader(new FileReader(template))) {
            try(PrintWriter writer = new PrintWriter(new FileWriter(output))) {
                reader.lines().forEach(l -> writer.println(l.replace("{exportedPackages}", packagesList)));
            }
        }
        Log.info("Written " + output.getAbsolutePath());
    }

    private void visit(File file, String packageName) {
        for(File child : Objects.requireNonNull(file.listFiles())) {
            if(child.isFile() && child.getName().endsWith(".java")) {
                packages.add(packageName);
            } else if(child.isDirectory()) {
                visit(child, (packageName.isEmpty() ? "" : packageName + ".") + child.getName());
            }
        }
    }
}
