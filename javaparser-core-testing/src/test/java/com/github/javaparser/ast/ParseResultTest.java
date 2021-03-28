/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.Node.Parsedness.PARSED;
import static com.github.javaparser.ast.Node.Parsedness.UNPARSABLE;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static org.assertj.core.api.Assertions.assertThat;

class ParseResultTest {
    private final JavaParser javaParser = new JavaParser(new ParserConfiguration());

    @Test
    void whenParsingSucceedsThenWeGetResultsAndNoProblems() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{}"));

        assertThat(result.getResult().isPresent()).isTrue();
        assertThat(result.getResult().get().getParsed()).isEqualTo(PARSED);
        assertThat(result.getProblems()).isEmpty();

        assertThat(result.toString()).isEqualTo("Parsing successful");
    }

    @Test
    void whenParsingFailsThenWeGetProblemsAndABadResult() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class {"));

        assertThat(result.getResult().isPresent()).isTrue();
        assertThat(result.getResult().get().getParsed()).isEqualTo(UNPARSABLE);
        assertThat(result.getProblems().size()).isEqualTo(1);

        Problem problem = result.getProblem(0);
        assertThat(problem.getMessage()).isEqualTo("Parse error. Found \"{\", expected one of  \"<:\" \"\\\\invariant_for\" \"\\\\old\" \"\\\\result\" \"abrupt_behavior\" \"abrupt_behaviour\" \"accessible\" \"accessible_redundantly\" \"also\" \"assert_redundantly\" \"assignable\" \"assignable_redundantly\" \"assume\" \"assume_redundantly\" \"axiom\" \"behavior\" \"behaviour\" \"break_behavior\" \"break_behaviour\" \"breaks\" \"breaks_redundantly\" \"callable\" \"callable_redundantly\" \"captures\" \"captures_redundantly\" \"choose\" \"choose_if\" \"code\" \"code_bigint_math\" \"code_java_math\" \"code_safe_math\" \"constraint\" \"constraint_redundantly\" \"constructor\" \"continue_behavior\" \"continue_behaviour\" \"continues\" \"continues_redundantly\" \"declassifies\" \"decreases\" \"decreases_redundantly\" \"decreasing\" \"decreasing_redundantly\" \"determines\" \"diverges\" \"diverges_redundantly\" \"duration_redundantly\" \"ensures\" \"ensures_free\" \"ensures_redundantly\" \"enum\" \"erases\" \"example\" \"exceptional_behavior\" \"exceptional_behaviour\" \"exceptional_example\" \"exports\" \"exsures\" \"exsures_redundantly\" \"extract\" \"field\" \"for_example\" \"forall\" \"ghost\" \"helper\" \"hence_by\" \"hence_by_redundantly\" \"implies_that\" \"in\" \"initializer\" \"initially\" \"instance\" \"invariant\" \"invariant_redundantly\" \"loop_invariant\" \"loop_invariant_redundantly\" \"maintaining\" \"maintaining_redundantly\" \"maps\" \"maps_redundantly\" \"measured_by\" \"measured_by_redundantly\" \"method\" \"model\" \"model_program\" \"modifiable\" \"modifiable_redundantly\" \"modifies\" \"modifies_redundantly\" \"module\" \"monitored\" \"monitors_for\" \"new_objects\" \"non_null\" \"normal_behavior\" \"normal_behaviour\" \"normal_example\" \"nullable\" \"nullable_by_default\" \"old\" \"open\" \"opens\" \"or\" \"post\" \"post_redundantly\" \"pre\" \"pre_redundantly\" \"provides\" \"pure\" \"readable\" \"refining\" \"represents\" \"represents_redundantly\" \"requires\" \"requires_free\" \"requires_redundantly\" \"return_behavior\" \"return_behaviour\" \"returns\" \"returns_redundantly\" \"set\" \"signals\" \"signals_only\" \"signals_only_redundantly\" \"signals_redundantly\" \"spec_bigint_math\" \"spec_java_math\" \"spec_package\" \"spec_private\" \"spec_protected\" \"spec_public\" \"spec_safe_math\" \"static_initializer\" \"strictfp\" \"strictly_pure\" \"to\" \"transitive\" \"uninitialized\" \"unreachable\" \"uses\" \"when\" \"when_redundantly\" \"with\" \"working_space\" \"working_space_redundantly\" \"writable\" \"yield\" <IDENTIFIER> <JML_IDENTIFIER>");
        assertThat(result.toString()).startsWith("Parsing failed:" + SYSTEM_EOL + "(line 1,col 1) Parse error.");
    }
}
