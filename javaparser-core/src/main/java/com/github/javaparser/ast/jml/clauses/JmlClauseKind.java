package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.jml.JmlKeyword;

import java.util.EnumSet;

public enum JmlClauseKind implements JmlKeyword {
    ENSURES(GeneratedJavaParserConstants.ENSURES),
    ENSURES_FREE(GeneratedJavaParserConstants.ENSURES_FREE),
    ENSURES_REDUNDANTLY(GeneratedJavaParserConstants.ENSURES_REDUNDANTLY),
    REQUIRES(GeneratedJavaParserConstants.REQUIRES),
    REQUIRES_FREE(GeneratedJavaParserConstants.REQUIRES_FREE),
    REQUIRES_REDUNDANTLY(GeneratedJavaParserConstants.REQUIRES_REDUNDANTLY),
    DECREASES(GeneratedJavaParserConstants.DECREASES),
    MODIFIES(GeneratedJavaParserConstants.MODIFIES),
    MODIFIABLE(GeneratedJavaParserConstants.MODIFIABLE),
    ASSIGNABLE(GeneratedJavaParserConstants.ASSIGNABLE),
    ACCESSIBLE(GeneratedJavaParserConstants.ACCESSIBLE),
    PRE(GeneratedJavaParserConstants.PRE),
    POST(GeneratedJavaParserConstants.POST),
    PRE_REDUNDANTLY(GeneratedJavaParserConstants.PRE_REDUNDANTLY),
    POST_REDUNDANTLY(GeneratedJavaParserConstants.POST_REDUNDANTLY),
    LOOP_INVARIANT(GeneratedJavaParserConstants.LOOP_INVARIANT),
    LOOP_INVARIANT_REDUNDANTLY(GeneratedJavaParserConstants.LOOP_INVARIANT_REDUNDANTLY),
    MEASURED_BY(GeneratedJavaParserConstants.MEASURED_BY),
    RETURNS(GeneratedJavaParserConstants.RETURNS),
    RETURNS_REDUNDANTLY(GeneratedJavaParserConstants.RETURNS_REDUNDANTLY),
    BREAKS(GeneratedJavaParserConstants.BREAKS),
    BREAKS_REDUNDANTLY(GeneratedJavaParserConstants.BREAKS_REDUNDANTLY),
    CONTINUES(GeneratedJavaParserConstants.CONTINUES),
    CONTINUES_REDUNDANTLY(GeneratedJavaParserConstants.CONTINUES_REDUNDANTLY),
    OLD(GeneratedJavaParserConstants.OLD),
    FORALL(GeneratedJavaParserConstants.FORALL),
    SIGNALS(GeneratedJavaParserConstants.SIGNALS),
    SIGNALS_REDUNDANTLY(GeneratedJavaParserConstants.SIGNALS_REDUNDANTLY),
    SIGNALS_ONLY(GeneratedJavaParserConstants.SIGNALS_ONLY),
    WHEN(GeneratedJavaParserConstants.WHEN),
    WORKING_SPACE(GeneratedJavaParserConstants.WORKING_SPACE),
    WORKING_SPACE_REDUNDANTLY(GeneratedJavaParserConstants.WORKING_SPACE_REDUNDANTLY),
    CAPTURES(GeneratedJavaParserConstants.CAPTURES),
    CAPTURES_REDUNDANTLY(GeneratedJavaParserConstants.CAPTURES_REDUNDANTLY),
    INITIALLY(GeneratedJavaParserConstants.INITIALLY),
    INVARIANT_REDUNDANTLY(GeneratedJavaParserConstants.INVARIANT_REDUNDANTLY),
    INVARIANT(GeneratedJavaParserConstants.INVARIANT),
    ASSIGNABLE_REDUNDANTLY(GeneratedJavaParserConstants.ASSIGNABLE_REDUNDANTLY),
    MODIFIABLE_REDUNDANTLY(GeneratedJavaParserConstants.MODIFIABLE_redundantly),
    MODIFIES_REDUNDANTLY(GeneratedJavaParserConstants.MODIFIES_redundantly),
    CALLABLE(GeneratedJavaParserConstants.CALLABLE),
    CALLABLE_REDUNDANTLY(GeneratedJavaParserConstants.CALLABLE_REDUNDANTLY),
    DIVERGES(GeneratedJavaParserConstants.DIVERGES),
    DIVERGES_REDUNDANTLY(GeneratedJavaParserConstants.DIVERGES_REDUNDANTLY),
    DURATION(GeneratedJavaParserConstants.DURATION),
    DURATION_REDUNDANTLY(GeneratedJavaParserConstants.DURATION_REDUNDANTLY);

    public final String jmlSymbol;
    private final int tokenType;

    JmlClauseKind(int tokenType) {
        this.tokenType = tokenType;
        jmlSymbol = name().toLowerCase();
    }

    JmlClauseKind(String jmlSymbol, int tokenType) {
        this.jmlSymbol = jmlSymbol;
        this.tokenType = tokenType;
    }

    @Override
    public String jmlSymbol() {
        return jmlSymbol;
    }

    public static EnumSet<JmlClauseKind> VALID_CLAUSES_BLOCK_CONTRACT = EnumSet.of(
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
            RETURNS,
            BREAKS,
            CONTINUES,
            OLD,
            FORALL,
            SIGNALS,
            SIGNALS_ONLY,
            WHEN,
            WORKING_SPACE,
            CAPTURES,
            INITIALLY,
            INVARIANT,
            ASSIGNABLE_REDUNDANTLY,
            MODIFIABLE_REDUNDANTLY,
            MODIFIES_REDUNDANTLY,
            CAPTURES_REDUNDANTLY,
            CALLABLE,
            DIVERGES,
            DURATION
    );
}
