package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * A validator that will call a collection of validators.
 */
public class Validators implements Validator {
    private final List<Validator> validators = new ArrayList<>();

    public Validators(Validator... validators) {
        this.validators.addAll(Arrays.asList(validators));
    }

    public List<Validator> getValidators() {
        return validators;
    }

    @Override
    public void validate(Node node, ProblemReporter problemReporter) {
        validators.forEach(v -> v.validate(node, problemReporter));
    }
}
