For the tests regarding resolving symbols in Jar files, we need some jar files. Some other tests within JavaSymbolSolver use established external jars for that purpose. Given the very specific cases we need here, that would severly complicate writing and maintaining tests. Therefore, I've decided to write custom jars for the cases we need.

`main_jar` contains most of the necessary classes, `included_jar` and `excluded_jar` both contain an interface and a superclass. Included_jar is included in the combined type solver, while excluded_jar is not.

Running the buildTestJarMainJar gradle task should rebuild all necessary files.
When you need to rebuild the jar, it is important to make sure you actually update the jar in git. Jar-files are in the git-ignore, so you'll have to force-add them using `git -f main_jar.jar`.

(`result` was chosen as a name instead of `target` or `out`, because those seem to be ignored.)