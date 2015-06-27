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

package com.github.javaparser.full.utils;

import junit.framework.AssertionFailedError;
import org.junit.runner.Description;
import org.junit.runner.Runner;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunNotifier;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Didier Villevalois
 */
public class BulkTestRunner extends Runner {

	private final BulkTestClass bulkTest;
	private final String testResourcesPath;
	private final List<String> directories;
	private final Description rootDescription;
	private final List<Description> scenariDescriptions = new ArrayList<Description>();

	private final ResourceHelper resourceHelper = ResourceHelper.classpathExcludingJre();

	public BulkTestRunner(Class<? extends BulkTestClass> testClass)
			throws Throwable {
		bulkTest = testClass.newInstance();

		String path = bulkTest.testResourcesPath();
		testResourcesPath = path + (path.endsWith("/") ? "" : "/");

		directories = new ArrayList<String>(resourceHelper.listDirectories(testResourcesPath));

		rootDescription = Description.createSuiteDescription(bulkTest.getClass());
		for (String directory : directories) {
			scenariDescriptions.add(Description.createTestDescription(testClass, directory));
		}
		rootDescription.getChildren().addAll(scenariDescriptions);
	}

	@Override
	public Description getDescription() {
		return rootDescription;
	}

	@Override
	public void run(RunNotifier notifier) {
		notifier.fireTestStarted(rootDescription);
		for (int i = 0; i < directories.size(); i++) {
			String directory = directories.get(i);
			Description description = scenariDescriptions.get(i);
			try {
				notifier.fireTestStarted(description);

				TestResources resources = new TestResources(resourceHelper, testResourcesPath, directory);
				bulkTest.runTest(resources);

				notifier.fireTestFinished(description);
			} catch (AssertionFailedError e) {
				notifier.fireTestAssumptionFailed(new Failure(description, e));
			} catch (IOException e) {
				notifier.fireTestFailure(new Failure(description, e));
			} catch (Throwable e) {
				notifier.fireTestFailure(new Failure(description, e));
			}
		}
		notifier.fireTestFinished(rootDescription);
	}
}
