package com.github.jmlparser;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.jmlparser.lint.JmlLintingConfig;
import com.github.jmlparser.lint.JmlLintingFacade;
import com.github.jmlparser.redux.ReduxPipeline;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (12/31/21)
 */
public class Main {
    private static final Args args = new Args();

    public static void main(String[] argv) {
        JCommander.newBuilder()
                .addObject(args)
                .build()
                .parse(argv);
        run();
    }

    private static void run() {
        ParserConfiguration config = createParserConfiguration(args);
        Collection<? extends Node> nodes = parse(args.files, config);
        if (args.lint) {
            lint(nodes);
        }

        if (args.transform) {
            ReduxPipeline pipeline = new ReduxPipeline();
            //TODO weigl writing to output directory
        }
    }

    private static void lint(Collection<? extends Node> nodes) {
        JmlLintingConfig lconfig = createLinterConfiguration(args);
        Collection<Problem> problems = JmlLintingFacade.lint(lconfig, nodes);
        for (Problem problem : problems) {
            report(problem);
        }
    }

    private static JmlLintingConfig createLinterConfiguration(Args args) {
        JmlLintingConfig config = new JmlLintingConfig();
        return config;
    }

    private static Collection<? extends Node> parse(List<String> files, ParserConfiguration config) {
        List<File> expanded = new ArrayList<>(files.size() * 10);
        for (String file : files) {
            File f = new File(file);
            if (f.isDirectory()) {
                expandDirectory(expanded, f);
            } else {
                expanded.add(f);
            }
        }

        return expanded.parallelStream()
                .map(it -> parse(it, config))
                .map(Main::reportOnError)
                .filter(Objects::nonNull)
                .collect(Collectors.toList());
    }

    private static CompilationUnit reportOnError(ParseResult<CompilationUnit> it) {
        final Optional<CompilationUnit> result = it.getResult();
        if (it.isSuccessful() && result.isPresent()) {
            return result.get();
        }
        for (Problem problem : it.getProblems()) {
            report(problem);
        }
        return null;
    }

    private static void report(Problem problem) {
        System.out.println(problem.toString());
    }

    private static void expandDirectory(Collection<File> target, File dir) {
        File[] files = dir.listFiles();
        if (files != null) {
            for (File file : files) {
                if (file.isDirectory()) {
                    expandDirectory(target, file);
                } else {
                    if (file.getName().endsWith(".java")) {
                        target.add(file);
                    }
                }
            }
        }
    }

    private static ParseResult<CompilationUnit>
    parse(File file, ParserConfiguration configuration) {
        JavaParser p = new JavaParser(configuration);
        try {
            return p.parse(file);
        } catch (FileNotFoundException e) {
            report(new Problem("File not found", null, e));
            return null;
        }
    }

    private static ParserConfiguration createParserConfiguration(Args args) {
        ParserConfiguration config = new ParserConfiguration();
        config.setJmlKeys(new TreeSet<>(args.activeJmlKeys));
        config.setProcessJml(!args.disableJml);
        return config;
    }

    static class Args {
        @Parameter
        public boolean lint = true;

        @Parameter
        public boolean transform;

        @Parameter
        private final List<String> files = new ArrayList<>();

        @Parameter()
        private final List<String> activeJmlKeys = new ArrayList<>();


        @Parameter(names = {"-verbose"}, description = "Level of verbosity")
        private final Integer verbose = 1;

        @Parameter()
        private final boolean disableJml = false;
    }
}
