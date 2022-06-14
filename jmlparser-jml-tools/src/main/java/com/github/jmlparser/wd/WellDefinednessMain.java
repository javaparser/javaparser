package com.github.jmlparser.wd;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.github.javaparser.ParserConfiguration;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.NullLogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.*;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (13.06.22)
 */
public class WellDefinednessMain {
    private static final Args args = new Args();

    public static void main(String[] argv) throws InterruptedException, SolverException, InvalidConfigurationException {
        JCommander cmd = JCommander.newBuilder()
                .programName("jml-wd")
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
            //config.getJmlKeys().add(new ArrayList<>());
            config.getJmlKeys().add(Collections.singletonList("key"));
            //config.getJmlKeys().add(Collections.singletonList("openjml"));
        }

        // Instantiate JavaSMT with SMTInterpol as backend (for dependencies cf. documentation)
        LogManager logger = NullLogManager.getInstance();
        ShutdownNotifier shutdownNotifier = ShutdownNotifier.createDummy();

        Configuration smtConfig = Configuration.defaultConfiguration();
        try (SolverContext context = SolverContextFactory.createSolverContext(
                smtConfig, logger, shutdownNotifier, SolverContextFactory.Solvers.SMTINTERPOL)) {
            WDVisitor wd = new WDVisitor(context);


            // Solve formula, get model, and print variable assignment
            try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
                //XXX
                boolean isUnsat = prover.isUnsat();
                assert !isUnsat;
                try (Model model = prover.getModel()) {
                    //System.out.printf("SAT with a = %s, b = %s", model.evaluate(a), model.evaluate(b));
                }
            }
        }
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
