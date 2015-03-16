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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import java.io.File;
import java.io.IOException;

/**
 * @author Didier Villevalois
 */
@RunWith(JUnit4.class)
public class Performance {

    private final Runtime runtime = Runtime.getRuntime();

    @Test
    public void testPerf() throws ParseException, IOException {
        File file = new File(getClass().getResource("bdd/samples/RandoopTest0.java").getPath());

        boolean[][] flags = {
                new boolean[]{false, false},
                new boolean[]{false, true},
                new boolean[]{true, false},
                new boolean[]{true, true},
        };

        for (int i = 0; i < flags.length; i++) {
            long start = freeMemory();
            CompilationUnit cu = JavaParser.parse(file, null, flags[i][0], flags[i][1]);
            long memory = start - freeMemory();

            // To force not being gc'ed in case of compiler optimization
            Assert.assertNotNull(cu);

            System.out.println("[attributeComments=" + flags[i][0] + ", preserveLexemes=" + flags[i][1] + "]");
            System.out.printf("  Used memory:  %.1fMB\n", ((double) memory) / 1024 / 1024);
        }

        parseNTimes(file, 100, flags);
    }

    private long freeMemory() {
        runtime.gc();
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
        }
        return runtime.freeMemory();
    }

    private void parseNTimes(File file,
                             int iterationCount,
                             boolean[][] flags)
            throws ParseException, IOException {
        Timer timer = new Timer();
        CompilationUnit cu = null;
        double[][] results = new double[flags.length][];
        for (int i = 0; i < flags.length; i++) {
            results[i] = new double[]{0.0, 0.0};
        }

        for (int j = 0; j < iterationCount; j++) {
            for (int i = 0; i < flags.length; i++) {
                timer.start();
                cu = JavaParser.parse(file, null, flags[i][0], flags[i][1]);
                results[i][0] += timer.stop();

                timer.start();
                cu.toString();
                results[i][1] += timer.stop();
            }
        }

        for (int i = 0; i < flags.length; i++) {
            System.out.println("[attributeComments=" + flags[i][0] + ", preserveLexemes=" + flags[i][1] + "]");
            System.out.printf("  Parse    - total: %.3fs; iteration: %.2fms\n", results[i][0] / 1000, results[i][0] / iterationCount);
            System.out.printf("  ToString - total: %.3fs; iteration: %.2fms\n", results[i][1] / 1000, results[i][1] / iterationCount);
        }
    }

    class Timer {
        private long start;

        public void start() {
            start = System.currentTimeMillis();
        }

        public double stop() {
            return ((double) (System.currentTimeMillis() - start));
        }
    }
}
