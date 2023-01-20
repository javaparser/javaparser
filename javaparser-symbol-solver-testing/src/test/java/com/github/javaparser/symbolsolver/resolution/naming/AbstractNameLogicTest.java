/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.*;
import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertTrue;

public abstract class AbstractNameLogicTest extends AbstractResolutionTest {

    protected Node getNameInCodeTollerant(String code, String name, ParseStart parseStart) {
        return getNameInCode(code, name, parseStart, true, Optional.empty());
    }

    protected Node getNameInCodeTollerant(String code, String name, ParseStart parseStart, TypeSolver typeSolver) {
        return getNameInCode(code, name, parseStart, true, Optional.of(typeSolver));
    }

    protected Node getNameInCode(String code, String name, ParseStart parseStart) {
        return getNameInCode(code, name, parseStart, false, Optional.empty());
    }

    protected <N extends Node> N parse(String code, ParseStart<N> parseStart) {
        return parse(code, parseStart, Optional.empty());
    }

    protected <N extends Node> N parse(String code, ParseStart<N> parseStart, Optional<TypeSolver> typeSolver) {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW);
        if (typeSolver.isPresent()) {
            parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver.get()));
        }
        ParseResult<N> parseResult = new JavaParser(parserConfiguration).parse(parseStart, new StringProvider(code));
        if (!parseResult.isSuccessful()) {
            parseResult.getProblems().forEach(p -> System.out.println("ERR: " + p));
        }
        assertTrue(parseResult.isSuccessful());
        N root = parseResult.getResult().get();
        return root;
    }

    private Node getNameInCode(String code, String name, ParseStart parseStart, boolean tollerant,
                               Optional<TypeSolver> typeSolver) {
        Node root = parse(code, parseStart, typeSolver);
        List<Node> allNames = root.findAll(Node.class).stream()
                .filter(NameLogic::isAName)
                .collect(Collectors.toList());
        List<Node> matchingNames = allNames.stream()
                .filter(n -> NameLogic.nameAsString(n).equals(name))
                .collect(Collectors.toList());
        // In case of one name being contained in other as is, we remove it
        for (int i=0;i<matchingNames.size();i++) {
            Node container = matchingNames.get(i);
            for (int j=i+1;j<matchingNames.size();j++) {
                Node contained = matchingNames.get(j);
                if (contained.getParentNode().isPresent() && contained.getParentNode().get() == container
                        && NameLogic.nameAsString(contained).equals(NameLogic.nameAsString(container))) {
                    matchingNames.remove(j);
                    j--;
                }
            }
        }

        if (matchingNames.size() == 0) {
            throw new IllegalArgumentException("Not found. Names found: " + String.join(", ",
                    allNames.stream().map(NameLogic::nameAsString).collect(Collectors.toList())));
        } else if (matchingNames.size() > 1) {
            if (tollerant) {
                return matchingNames.get(matchingNames.size() - 1);
            } else {
                throw new IllegalArgumentException("Ambiguous: there are several matching.");
            }
        } else {
            return matchingNames.get(0);
        }
    }

}
