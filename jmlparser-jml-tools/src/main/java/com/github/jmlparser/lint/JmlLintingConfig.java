package com.github.jmlparser.lint;

import lombok.Data;
import lombok.Getter;
import lombok.Setter;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
@Data
public class JmlLintingConfig {
    private boolean checkNameClashes = true;
    private boolean checkMissingNames = true;

    public JmlLintingConfig() {
    }

    public boolean isDisabled(LintRule lintRule) {
        return false;
    }
}
