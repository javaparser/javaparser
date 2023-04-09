package com.github.jmlparser;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.jmlparser.jml2java.J2JCommand;
import com.github.jmlparser.lint.JmlLintingConfig;
import com.github.jmlparser.lint.JmlLintingFacade;
import com.github.jmlparser.lint.LintCommand;
import com.github.jmlparser.lint.LintProblem;
import com.github.jmlparser.pp.PrettyPrintCommand;
import com.github.jmlparser.stat.StatCommand;
import com.github.jmlparser.wd.WdCommand;
import com.github.jmlparser.xpath.XPathCommand;

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
        final var j2j = new J2JCommand();
        final var lint = new LintCommand();
        final var pp = new PrettyPrintCommand();
        final var stat = new StatCommand();
        final var xpath = new XPathCommand();
        final var wd = new WdCommand();
        var jc = JCommander.newBuilder()
                .addCommand(j2j)
                .addCommand(lint)
                .addCommand(pp)
                .addCommand(stat)
                .addCommand(xpath)
                .addCommand(wd)
                .addObject(args)
                .build();
        jc.parse(argv);

        ParserConfiguration config = createParserConfiguration(args);
        //Collection<? extends Node> nodes = parse(args.files, config);

        String parsedCmdStr = jc.getParsedCommand();
        if (parsedCmdStr == null) {
            System.err.println("Invalid command: " + parsedCmdStr);
            jc.usage();
        } else {
            switch (parsedCmdStr) {
                case "pp":
                    pp.run();
                    break;
                case "wd":
                    wd.run();
                    break;
                default:
                    System.err.println("Invalid command: " + parsedCmdStr);
                    jc.usage();
            }
        }
    }

    private static void lint(Collection<? extends Node> nodes) {
        JmlLintingConfig lconfig = createLinterConfiguration(args);
        var problems = new JmlLintingFacade(lconfig).lint(nodes);
        for (var problem : problems) {
            report(problem);
        }
    }

    private static JmlLintingConfig createLinterConfiguration(Args args) {
        return new JmlLintingConfig();
    }

    public static Collection<CompilationUnit> parse(List<String> files, ParserConfiguration config) {
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

    private static void report(LintProblem problem) {
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
        config.getJmlKeys().add(new ArrayList<>(args.activeJmlKeys));
        config.setProcessJml(!args.disableJml);
        return config;
    }

    static class Args {
        @Parameter(names = {"--jml-keys"})
        private List<String> activeJmlKeys = new ArrayList<>();


        @Parameter(names = {"-verbose"}, description = "Level of verbosity")
        private Integer verbose = 1;

        @Parameter(names = {"--disable-jml"})
        private boolean disableJml = false;
    }
}
