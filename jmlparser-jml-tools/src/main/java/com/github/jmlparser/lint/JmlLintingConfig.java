package com.github.jmlparser.lint;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlLintingConfig {
    private boolean checkNameClashes = true;
    private boolean checkMissingNames = true;

    public JmlLintingConfig() {
    }

    public boolean isCheckNameClashes() {
        return checkNameClashes;
    }

    public void setCheckNameClashes(boolean checkNameClashes) {
        this.checkNameClashes = checkNameClashes;
    }

    public boolean isCheckMissingNames() {
        return checkMissingNames;
    }

    public void setCheckMissingNames(boolean checkMissingNames) {
        this.checkMissingNames = checkMissingNames;
    }

    public boolean isDisabled(LintRule lintRule) {
        return false;
    }
}
