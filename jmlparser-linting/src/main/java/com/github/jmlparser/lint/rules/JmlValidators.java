package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.validator.Validators;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlValidators extends Validators {
    public static Validators getJmlValidators() {
        Validators v = new Validators();
        v.add(new JmlNameClashWithJava());
        return v;
    }
}
