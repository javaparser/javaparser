## Getting started

Here is some information that's good to know when contributing to JavaParser:

- There is some interesting information on the [wiki](https://github.com/javaparser/javaparser/wiki).
- We work on JavaParser because we like to, not because it earns us money. Please remember that we try to run a
  professional project in our spare time, on a budget of zero.
- Be sure to check [the coding guidelines](https://github.com/javaparser/javaparser/wiki/Coding-Guidelines) which are
  easily used by installing the formatting rules as described there.
- If you're new and like to casually contribute something, check out
  the [easy issues](https://github.com/javaparser/javaparser/labels/Easy).
- If you're new and would like to become a member, start your own project that uses JavaParser.
  We noticed we get the best feedback from those.
  Here are [some fun project ideas](https://github.com/javaparser/javaparser/labels/fun%20project%20idea).
- If you start working on an issue, please say so with a comment in the issue.
- If you know how to fix a problem, please fix it and open a pull request instead of opening an issue.
- If you would like to add new nodes, or new fields to existing nodes, check out the [Guide to Adding New Nodes and Fields](https://github.com/javaparser/javaparser/wiki/A-Detailed-Guide-to-Adding-New-Nodes-and-Fields).

Thanks for helping!

## Contribution Workflow

Our development workflow is based on Pull Request. If you are not familiar with the Pull Requests, we suggest you to
checkout the [Github Documentation](https://help.github.com/articles/creating-a-pull-request/) for more information.

1. **Fork** the JavaParser project. If you already have a fork, ensure to fetch the latest commits.
2. In your forked project, **create a branch** related to the issue you are working on. This is important to ensure that
   your pull request will not contain unrelated work.
3. When your work in your branch is done, **push your branch to your forked repository**.
4. Go back to the [javaparser project site](https://github.com/javaparser/javaparser) and it should have a message
   offering to **create a pull request**. If it doesn't you
   can [create one manually](https://github.com/javaparser/javaparser/compare).

### Remember:

- A pull request should include tests. You can either use BDD or JUnit.
- Every pull request will automatically be checked by a few tools. Make sure AppVeyor and Travis are green.
- Pull requests often stay open for at least a few days to give people a chance to review it.
- A pull request is merged when all comments on it have been resolved.
- If you create a pull request for an issue, mention the issue in the format #123 to make github link it automatically.
- Before creating a commit (or at least before submitting a pull request), please reformat the project with the instructions given below
  to avoid any formatting-related issues during the review.

### Note on formatting the project:

- If you are developing on a machine with bash installed, execute `./run_core_metamodel_generator.sh && ./run_core_generators.sh`. This
  will re-run all of the code generators and then re-format the entire project as a final step. This ensures that:
  - All the code that needs to be generated has been generated correctly.
  - None of the changes you've added will be overwritten by code generation in the future.
  - All of your changes are correctly formatted (including changes made during code generation, for example whitespace changes).

  The PR check for style runs these generators and checks that the diff after doing so is empty, so if you've run this on your machine,
  then that check should not fail.

- If you are developing on a machine without bash, execute `./mvnw spotless:apply`. This will re-format the project, but without
  running the code generators. This will be sufficient in many cases, but it's still possible that changes are introduced during
  code generation which would cause the PR style check to fail. If this happens, some manual changes are required.

  To fix this:
  1. Go to the job output for the failed `Spotless check` job by clicking the red cross next to the job.
  2. Scroll to the bottom of the `Generate code and format` output tab. 
  3. There, you will see output from the diff command showing what failed. For example, in https://github.com/javaparser/javaparser/actions/runs/10389076737/job/28766249645,
     that output is:
    ```
    [INFO] ------------------------------------------------------------------------
    diff --git a/javaparser-core/src/main/java/com/github/javaparser/ast/expr/RecordPatternExpr.java b/javaparser-core/src/main/java/com/github/javaparser/ast/expr/RecordPatternExpr.java
    index 7bc7f46b9..429889e35 100644
    --- a/javaparser-core/src/main/java/com/github/javaparser/ast/expr/RecordPatternExpr.java
    +++ b/javaparser-core/src/main/java/com/github/javaparser/ast/expr/RecordPatternExpr.java
    @@ -17,7 +17,6 @@
      * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
      * GNU Lesser General Public License for more details.
      */
    -
     package com.github.javaparser.ast.expr;
     
     import static com.github.javaparser.utils.Utils.assertNotNull;
    Error: Process completed with exit code 1.
    ```

  4. Verify that this output does not overwrite any code you wrote which would change the behaviour. If it does, you probably implemented
     something manually when it should've been generated and this will be overwritten next time the code generators are run. This requires
     a manual fix to your code to prevent issues in the future.
  5. If no major issues are found, copy this output, excluding the `[INFO] --...` line and the `Error: Process complete with exit code 1.` 
     line and paste that into a patch file (for example, `/tmp/style.patch`, but the name and location aren't important).
  6. From the javaparser project directory, run `git apply /tmp/style.patch` (substituting `/tmp/style.patch` for the path of your
     patch file). `git status` should now show that all the files mentioned in the patch are modified.
  7. Add and commit the changes and push to update the PR.
