/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.bdd;

import com.github.javaparser.bdd.steps.SharedSteps;
import com.github.javaparser.bdd.steps.VisitorSteps;
import de.codecentric.jbehave.junit.monitoring.JUnitReportingRunner;
import org.jbehave.core.steps.InjectableStepsFactory;
import org.jbehave.core.steps.InstanceStepsFactory;
import org.junit.runner.RunWith;

import java.util.HashMap;
import java.util.Map;

@RunWith(JUnitReportingRunner.class)
public class VisitorTest extends BasicJBehaveTest {

    @Override
    public InjectableStepsFactory stepsFactory() {
        Map<String, Object> state = new HashMap<>();
        return new InstanceStepsFactory(configuration(),
                new SharedSteps(state),
                new VisitorSteps(state));
    }

    public VisitorTest() {
        super("**/bdd/visitor*.story");
    }
}



