package com.github.jmlparser.lint;

import com.github.javaparser.ast.Node;
import com.github.jmlparser.lint.sarif.*;
import lombok.Getter;
import org.jetbrains.annotations.NotNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.Exception;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlLintingFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(JmlLintingFacade.class);
    private static final String VERSION = JmlLintingFacade.class.getPackage().getImplementationVersion();
    private static final String NAME = "JML-lint";

    @Getter
    private final List<LintRule> linters;
    private final JmlLintingConfig config;

    public JmlLintingFacade(JmlLintingConfig config) {
        linters = getLinter(config);
        this.config = config;
    }

    private Tool getSarifTool() {
        return new Tool(
                new ToolComponent().withVersion(VERSION).withName(NAME)
                        .withShortDescription(new MultiformatMessageString().withText("Linting for the Java Modeling Language")),
                linters.stream().map(it -> new ToolComponent().withFullName(it.getClass().getName())).collect(Collectors.toSet()),
                new PropertyBag()
        );
    }


    private static List<LintRule> getLinter(JmlLintingConfig config) {
        ServiceLoader<LintRule> loader = ServiceLoader.load(LintRule.class);
        List<LintRule> validators = new ArrayList<>(64);
        for (LintRule lintRule : loader) {
            if (!config.isDisabled(lintRule)) {
                validators.add(lintRule);
            }
        }
        return validators;
    }

    public void lint(LintProblemReporter reporter, Collection<? extends Node> nodes) {
        for (Node it : nodes) {
            for (LintRule linter : linters) {
                try {
                    linter.accept(it, reporter, config);
                } catch (Exception e) {
                    LOGGER.error("Error in linter: {}", linter.getClass().getName(), e);
                }
            }
        }
    }

    public Collection<LintProblem> lint(@NotNull Collection<? extends Node> nodes) {
        var problems = new ArrayList<LintProblem>(1024);
        Consumer<LintProblem> collector = problems::add;
        lint(new LintProblemReporter(collector), nodes);
        problems.sort(Comparator.comparing(it -> it.location().toRange().get().begin));
        return problems;
    }

    public SarifSchema asSarif(Collection<LintProblem> problems) throws URISyntaxException {
        List<Result> results = problems.stream().map(this::asSarif).toList();
        List<Run> runs = List.of(new Run().withTool(getSarifTool()).withResults(results));
        return new SarifSchema(
                new URI("http://json.schemastore.org/sarif-2.1.0-rtm.4"),
                "2.1.0",
                runs, Set.of(), new PropertyBag());
    }

    private Result asSarif(LintProblem it) {
        return new Result().withRuleId(it.ruleId()).withKind(it.category()).withLevel(it.level())
                .withLocations(List.of(new Location())).withMessage(new Message().withText(it.message()));
    }
}
