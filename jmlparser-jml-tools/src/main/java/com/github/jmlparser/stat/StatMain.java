package com.github.jmlparser.stat;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.jmlparser.Main;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
public class StatMain {
    private static final Args args = new Args();

    public static void main(String[] argv) {
        JCommander cmd = JCommander.newBuilder()
                .programName("jml-stat")
                .addObject(args)
                .build();
        cmd.parse(argv);

        if (args.help) {
            cmd.usage();
            return;
        }

        ParserConfiguration config = new ParserConfiguration();
        config.setProcessJml(true);
        config.setKeepJmlDocs(true);
        for (String activeJmlKey : args.activeJmlKeys) {
            String[] activeJmlKeys = activeJmlKey.split(",");
            config.getJmlKeys().add(Arrays.asList(activeJmlKeys));
        }

        if (args.activeJmlKeys.isEmpty()) {
            config.getJmlKeys().add(new ArrayList<>());
            config.getJmlKeys().add(Collections.singletonList("key"));
            config.getJmlKeys().add(Collections.singletonList("openjml"));
        }

        Collection<CompilationUnit> nodes = Main.parse(args.files, config);
        StatVisitor statVisitor = new StatVisitor(config.getJmlKeys());
        for (CompilationUnit node : nodes) {
            node.accept(statVisitor, null);
        }

        Gson gson = new GsonBuilder().setPrettyPrinting().create();
        System.out.println(gson.toJson(statVisitor.getNewlines()));
    }

    private static class Args {
        @Parameter
        private List<String> files = new ArrayList<>();

        @Parameter(names = "-k")
        private List<String> activeJmlKeys = new ArrayList<>();

        @Parameter(names = "-h")
        private boolean help = false;


        @Parameter(names = {"-verbose"}, description = "Level of verbosity")
        private Integer verbose = 1;
    }
}
