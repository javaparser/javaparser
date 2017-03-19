package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.validator.chunks.CommonValidators;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

import java.util.Optional;

public class Java1_0Validator extends Validators {
    public Java1_0Validator() {
        super(
                new CommonValidators(),
                new ModifierValidator(false)
        );
    }
}
