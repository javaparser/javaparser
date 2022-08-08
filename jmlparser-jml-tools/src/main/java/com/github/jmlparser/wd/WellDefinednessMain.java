package com.github.jmlparser.wd;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.Expression;
import com.github.jmlparser.smt.ArithmeticTranslator;
import com.github.jmlparser.smt.BitVectorArithmeticTranslator;
import com.github.jmlparser.smt.SmtQuery;
import com.github.jmlparser.smt.SmtTermFactory;
import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.solver.Solver;
import com.github.jmlparser.smt.solver.SolverAnswer;
import lombok.SneakyThrows;

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

    public static void main(String[] argv) {
        JCommander cmd = JCommander.newBuilder().programName("jml-wd").addObject(args).build();
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
            config.getJmlKeys().add(Collections.singletonList("key"));
        }

        WDVisitor wd = new WDVisitor();
    }

    public static boolean isWelldefined(String expr) {
        ParserConfiguration config = new ParserConfiguration();
        config.setProcessJml(false);
        JavaParser parser = new JavaParser(config);
        return isWelldefined(parser, expr);
    }

    public static boolean isWelldefined(JavaParser parser, String expr) {
        ParseResult<Expression> e = parser.parseJmlExpression(expr);
        if (e.isSuccessful() && e.getResult().isPresent()) {
            return isWelldefined(e.getResult().get());
        }
        return false;
    }

    @SneakyThrows
    private static boolean isWelldefined(Expression e) {
        SmtQuery query = new SmtQuery();
        ArithmeticTranslator translator = new BitVectorArithmeticTranslator(query);
        WDVisitorExpr visitor = new WDVisitorExpr(query, translator);
        SExpr res = e.accept(visitor, null);
        if ("true".equals(res.toString())) {
            return true;
        }
        query.addAssert(SmtTermFactory.INSTANCE.not(res));
        query.checkSat();
        Solver solver = new Solver();
        SolverAnswer ans = solver.run(query);
        System.out.println(query.toString());
        System.out.println(ans.toString());
        ans.consumeErrors();
        return ans.isSymbol("unsat");
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
