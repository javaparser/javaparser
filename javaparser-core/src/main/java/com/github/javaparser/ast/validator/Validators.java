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

    public Validators remove(Validator validator) {
        if (!validators.remove(validator)) {
            throw new AssertionError("Trying to remove a validator that isn't there.");
        }
        return this;
    }

    public Validators replace(Validator oldValidator, Validator newValidator) {
        remove(oldValidator);
        add(newValidator);
        return this;
    }

    public Validators add(Validator newValidator) {
        validators.add(newValidator);
        return this;
    }

    @Override
    public void accept(Node node, ProblemReporter problemReporter) {
        validators.forEach(v -> v.accept(node, problemReporter));
    }
}
