/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;
import com.github.javaparser.utils.Utils;

/**
 * This represents a change that has happened to a specific Node.
 */
public interface Change {

    default boolean evaluate(CsmConditional csmConditional, Node node) {
        switch(csmConditional.getCondition()) {
            case FLAG:
                return csmConditional.getProperties().stream().anyMatch(p -> (Boolean) getValue(p, node));
            case IS_NOT_EMPTY:
                return !Utils.valueIsNullOrEmpty(getValue(csmConditional.getProperty(), node));
            case IS_EMPTY:
                return Utils.valueIsNullOrEmpty(getValue(csmConditional.getProperty(), node));
            case IS_PRESENT:
                return !Utils.valueIsNullOrEmptyStringOrOptional(getValue(csmConditional.getProperty(), node)) && !isEvaluatedOnDerivedProperty(csmConditional.getProperty());
            default:
                throw new UnsupportedOperationException("" + csmConditional.getProperty() + " " + csmConditional.getCondition());
        }
    }

    /*
	 * Evaluate on derived property.
	 *
	 * Currently the evaluation of the conditions is carried out in relation to the
	 * presence of value in the field/attribute of a class referenced by a property
	 * (for example the BODY property is referenced to the body field in the
	 * LambdaExpr class) but this is not quite correct.
	 *
	 * Indeed, there are attributes that are derived. The meaning of a derived
	 * attribute (annotated with the DerivedProperty annotation) is not very clear.
	 * Assuming that it is an existing attribute and accessible by another property,
	 * for example this is the case for the EXPRESSION_BODY property which allows
	 * access to a derived field (which is also accessible by the BODY property).
	 *
	 * The 2 properties EXPRESSION_BODY and BODY have a different meaning because
	 * one references a simple expression while the other references a list of
	 * expressions (this distinction is particularly interesting in the case of
	 * lambda expressions).
	 *
	 * In this particular case, the verification of the condition defined in the
	 * syntax model used by LPP must not succeed if the nature of the property is
	 * modified. So if we modify a lamba expression composed of a single expression
	 * by replacing it with a list of expressions, the evaluation of a condition
	 * relating to the presence of the EXPRESSION_BODY property, which makes it
	 * possible to determine the nature of the change, cannot not lead to a verified
	 * proposition which could be the case if we only consider that the field
	 * referenced by the EXPRESSION_BODY property has an acceptable value before the
	 * actual modification.
	 *
	 * This is why we also check if it is a derived property whose name coincides
	 * (*) with the updated property. If this is the case, we admit that the
	 * verification of the condition must fail so that we can execute the else
	 * clause of the condition. I'm not sure this issue #3949 is completely resolved
	 * by this change.
	 *
	 * (*) Assuming that by convention the derived property is suffixed with the
	 * name of the property it derives from (e.g.. EXPRESSION_BODY which matches an
	 * expression would derive from BODY which matches a list of expressions), we
	 * could deduce that EXPRESSION_BODY and BODY actually represent the same field
	 * but the validation condition must not be checked.
	 */
    default boolean isEvaluatedOnDerivedProperty(ObservableProperty property) {
        ObservableProperty currentProperty = getProperty();
        /*
		 * By convention we admit that the derived property is suffixed with the name of
		 * the property it derives from (e.g. EXPRESSION_BODY which matches an
		 * expression would derive from BODY which matches a list of expressions), so we
		 * could deduce that EXPRESSION_BODY and BODY actually represent the same
		 * field but the validation condition must not be checked.
		 * Be careful because NoChange property must not affect this evaluation.
		 */
        return currentProperty != null && (property.isDerived() && property.name().endsWith(currentProperty.name()));
    }

    /*
	 * Assuming that by convention the derived property is suffixed
	 * with the name of the property it derives from (e.g. EXPRESSION_BODY which
	 * matches an expression vs a list of expressions would derive from BODY) We
	 * could deduce that EXPRESSION_BODY and BODY actually represent the same
	 * property but the validation condition is not checked.
	 */
    ObservableProperty getProperty();

    Object getValue(ObservableProperty property, Node node);
}
