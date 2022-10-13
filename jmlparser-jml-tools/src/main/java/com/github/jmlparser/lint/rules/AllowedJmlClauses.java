package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.stmt.*;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRuleVisitor;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import static com.github.javaparser.ast.jml.clauses.JmlClauseKind.*;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public class AllowedJmlClauses extends LintRuleVisitor {
    public static final EnumSet<JmlClauseKind> METHOD_CONTRACT_CLAUSES = EnumSet.of(
            ENSURES,
            ENSURES_FREE,
            ENSURES_REDUNDANTLY,
            REQUIRES,
            REQUIRES_FREE,
            REQUIRES_REDUNDANTLY,
            DECREASES,
            MODIFIES,
            MODIFIABLE,
            ASSIGNABLE,
            ACCESSIBLE,
            PRE,
            POST,
            PRE_REDUNDANTLY,
            POST_REDUNDANTLY,
            DECREASING,
            DECREASES_REDUNDANTLY,
            MEASURED_BY,
            OLD,
            FORALL,
            SIGNALS,
            SIGNALS_REDUNDANTLY,
            SIGNALS_ONLY,
            WHEN,
            WORKING_SPACE,
            WORKING_SPACE_REDUNDANTLY,
            CAPTURES,
            CAPTURES_REDUNDANTLY,
            ASSIGNABLE_REDUNDANTLY,
            MODIFIABLE_REDUNDANTLY,
            MODIFIES_REDUNDANTLY,
            CALLABLE,
            CALLABLE_REDUNDANTLY,
            DIVERGES,
            DIVERGES_REDUNDANTLY,
            DURATION,
            DURATION_REDUNDANTLY
    );

    private EnumSet<JmlClauseKind> LOOP_INVARIANT_CLAUSES = EnumSet.of(
            DECREASES,
            MODIFIES,
            MODIFIABLE,
            ASSIGNABLE,
            ACCESSIBLE,
            MAINTAINING,
            MAINTAINING_REDUNDANTLY,
            DECREASING,
            DECREASES_REDUNDANTLY,
            LOOP_INVARIANT,
            LOOP_INVARIANT_FREE,
            LOOP_INVARIANT_REDUNDANTLY
    );

    private EnumSet<JmlClauseKind> LOOP_CONTRACT_CLAUSES = EnumSet.of(
            ENSURES,
            ENSURES_FREE,
            ENSURES_REDUNDANTLY,
            REQUIRES,
            REQUIRES_FREE,
            REQUIRES_REDUNDANTLY,
            DECREASES,
            MODIFIES,
            MODIFIABLE,
            ASSIGNABLE,
            ACCESSIBLE,
            PRE,
            POST,
            PRE_REDUNDANTLY,
            POST_REDUNDANTLY,
            MAINTAINING,
            MAINTAINING_REDUNDANTLY,
            DECREASING,
            DECREASES_REDUNDANTLY,
            LOOP_INVARIANT,
            LOOP_INVARIANT_FREE,
            LOOP_INVARIANT_REDUNDANTLY,
            MEASURED_BY,
            RETURNS,
            RETURNS_REDUNDANTLY,
            BREAKS,
            BREAKS_REDUNDANTLY,
            CONTINUES,
            CONTINUES_REDUNDANTLY,
            OLD,
            FORALL,
            SIGNALS,
            SIGNALS_REDUNDANTLY,
            SIGNALS_ONLY,
            WHEN,
            WORKING_SPACE,
            WORKING_SPACE_REDUNDANTLY,
            CAPTURES,
            CAPTURES_REDUNDANTLY,
            INITIALLY,
            INVARIANT_REDUNDANTLY,
            INVARIANT,
            ASSIGNABLE_REDUNDANTLY,
            MODIFIABLE_REDUNDANTLY,
            MODIFIES_REDUNDANTLY,
            CALLABLE,
            CALLABLE_REDUNDANTLY,
            DIVERGES,
            DIVERGES_REDUNDANTLY,
            DURATION,
            DURATION_REDUNDANTLY
    );

    private EnumSet<JmlClauseKind> BLOCK_CONTRACT_CLAUSES = EnumSet.of(
            ENSURES,
            ENSURES_FREE,
            ENSURES_REDUNDANTLY,
            REQUIRES,
            REQUIRES_FREE,
            REQUIRES_REDUNDANTLY,
            DECREASES,
            MODIFIES,
            MODIFIABLE,
            ASSIGNABLE,
            ACCESSIBLE,
            PRE,
            POST,
            PRE_REDUNDANTLY,
            POST_REDUNDANTLY,
            MAINTAINING,
            MAINTAINING_REDUNDANTLY,
            DECREASING,
            DECREASES_REDUNDANTLY,
            LOOP_INVARIANT,
            LOOP_INVARIANT_FREE,
            LOOP_INVARIANT_REDUNDANTLY,
            MEASURED_BY,
            RETURNS,
            RETURNS_REDUNDANTLY,
            BREAKS,
            BREAKS_REDUNDANTLY,
            CONTINUES,
            CONTINUES_REDUNDANTLY,
            OLD,
            FORALL,
            SIGNALS,
            SIGNALS_REDUNDANTLY,
            SIGNALS_ONLY,
            WHEN,
            WORKING_SPACE,
            WORKING_SPACE_REDUNDANTLY,
            CAPTURES,
            CAPTURES_REDUNDANTLY,
            INITIALLY,
            INVARIANT_REDUNDANTLY,
            INVARIANT,
            ASSIGNABLE_REDUNDANTLY,
            MODIFIABLE_REDUNDANTLY,
            MODIFIES_REDUNDANTLY,
            CALLABLE,
            CALLABLE_REDUNDANTLY,
            DIVERGES,
            DIVERGES_REDUNDANTLY,
            DURATION,
            DURATION_REDUNDANTLY
    );

    private Set<JmlClauseKind> currentlyAllowed = new HashSet<>();

    @Override
    public void visit(JmlContract n, LintProblemReporter arg) {
        Optional<NodeWithContracts> a = n.findAncestor(NodeWithContracts.class);
        if (a.isPresent()) {
            var owner = a.get();
            if (owner instanceof ForEachStmt
                    || owner instanceof ForStmt
                    || owner instanceof WhileStmt
                    || owner instanceof DoStmt) {
                if (n.getType() == JmlContract.Type.LOOP_INV)
                    checkClauses(arg, n.getClauses(), LOOP_INVARIANT_CLAUSES, "loop_invariant");
                else
                    checkClauses(arg, n.getClauses(), LOOP_CONTRACT_CLAUSES, "loop");
            } else if (owner instanceof MethodDeclaration) {
                checkClauses(arg, n.getClauses(), METHOD_CONTRACT_CLAUSES, "method");
            } else if (owner instanceof BlockStmt) {
                checkClauses(arg, n.getClauses(), BLOCK_CONTRACT_CLAUSES, "block");
            }
        }
    }

    private void checkClauses(LintProblemReporter arg, NodeList<JmlClause> clauses,
                              EnumSet<JmlClauseKind> allowed, String type) {
        for (JmlClause clause : clauses) {
            if (!allowed.contains(clause.getKind())) {
                arg.warn(clause, "%s clause not allowed in a %s contract", clause.getKind(), type);
            }
        }
    }
}
