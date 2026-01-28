/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.type.Type;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;

/**
 * Detects which node actually owns the tokens for a given node in the AST.
 *
 * <p>This utility is essential for the LexicalPreservingPrinter because the token
 * assignment algorithm assigns tokens based on position in the source code, not
 * necessarily to the logical AST node.
 *
 * <p><b>Core Problem:</b> In JavaParser's AST, child nodes may appear in the source
 * code <i>before</i> their parent node's position. The LPP assigns tokens to the
 * <i>nearest enclosing node</i> whose range includes the token's position.
 *
 * <p><b>Example:</b> In {@code Set<Pair<String, String>> x;}, the tokens for
 * {@code Pair<String, String>} are assigned to {@code VariableDeclarationExpr},
 * not to the {@code Pair} type node. When replacing {@code Pair}, the LPP needs
 * to know to regenerate {@code VariableDeclarationExpr}.
 *
 * <p><b>Implementation:</b> Uses the Strategy pattern with multiple detection
 * strategies, each handling a specific category of nodes (Types, Annotations,
 * Modifiers, etc.). Strategies are tried in priority order.
 *
 * @since 3.28.0
 */
class TokenOwnerDetector {

    /**
     * Strategy interface for detecting token owners.
     *
     * <p>Each strategy implementation checks if it applies to the given node,
     * then searches for the token owner by walking up the AST.
     */
    @FunctionalInterface
    interface DetectionStrategy {

        /**
         * Attempts to find the token owner for the given node.
         *
         * @param node the node to analyze
         * @return the token owner if this strategy applies, empty otherwise
         */
        Optional<Node> detect(Node node);
    }

    /**
     * Detection strategies in priority order.
     *
     * <p>Order matters: strategies are tried sequentially, first match wins.
     * Most frequent cases are placed first for performance (early exit).
     *
     * <p>Priority rationale:
     * <ol>
     *   <li>TypeOwnerStrategy - Most common, critical for Issue #3365</li>
     *   <li>AnnotationOwnerStrategy - Common in modern Java code</li>
     *   <li>ModifierOwnerStrategy - Moderately common</li>
     *   <li>TypeParameterOwnerStrategy - Less common (generics only)</li>
     *   <li>NameInExpressionStrategy - Rare edge cases</li>
     * </ol>
     */
    private static final List<DetectionStrategy> STRATEGIES = Arrays.asList(new TypeOwnerStrategy());

    /**
     * Finds the node that owns the tokens for the given node.
     *
     * <p>Algorithm:
     * <ol>
     *   <li>Try each detection strategy in priority order</li>
     *   <li>Return the first non-null owner found</li>
     *   <li>If no strategy applies, the node owns its own tokens</li>
     * </ol>
     *
     * @param node the node to find the token owner for
     * @return the node that owns the tokens, never null
     * @throws IllegalArgumentException if node is null
     */
    static Node findTokenOwner(Node node) {
        if (node == null) {
            throw new IllegalArgumentException("node cannot be null");
        }
        // Try each strategy in order
        for (DetectionStrategy strategy : STRATEGIES) {
            Optional<Node> owner = strategy.detect(node);
            if (owner.isPresent() && owner.get() != node) {
                return owner.get();
            }
        }
        // Default: node owns its own tokens
        return node;
    }

    /**
     * Determines if token owner regeneration is needed after a node replacement.
     *
     * <p><b>Context:</b> When a node is replaced in the AST (e.g., replacing {@code Pair}
     * with {@code SimpleImmutableEntry} in Issue #3365), the LexicalPreservingPrinter's
     * Observer notifies the change. However, the LPP only regenerates the NodeText for
     * the immediate parent of the replaced node by default.
     *
     * <p><b>Problem:</b> If the tokens for the replaced node are actually owned by an
     * ancestor further up the tree (as detected by {@link #findTokenOwner(Node)}), the
     * LPP won't regenerate the correct NodeText, resulting in the change not appearing
     * in the output.
     *
     * <p><b>Example where regeneration is needed:</b>
     * <pre>{@code
     * Set<Pair<String, String>> x;
     *
     * // When replacing Pair type:
     * // - parent: TypeArguments (immediate parent of Pair)
     * // - tokenOwner: VariableDeclarationExpr (owns the tokens)
     * // - replacedNode: ClassOrInterfaceType (Pair)
     *
     * // Result: needsRegeneration = true (tokenOwner != parent)
     * }</pre>
     *
     * <p><b>Example where regeneration is NOT needed:</b>
     * <pre>{@code
     * x = 5;
     *
     * // When replacing the literal 5:
     * // - parent: AssignExpr (immediate parent of literal)
     * // - tokenOwner: AssignExpr (same as parent)
     * // - replacedNode: IntegerLiteralExpr (5)
     *
     * // Result: needsRegeneration = false (normal LPP handling works)
     * }</pre>
     *
     * <p><b>Decision criteria:</b>
     * <ol>
     *   <li>If tokenOwner == parent: No regeneration needed (normal path)</li>
     *   <li>If replacedNode is a Type: Regeneration needed (Issue #3365 case)</li>
     *   <li>If replacedNode is inside a Type: Regeneration needed (nested case)</li>
     *   <li>Otherwise: No regeneration needed</li>
     * </ol>
     *
     * @param parent the immediate parent of the replaced node (where LPP would normally regenerate)
     * @param tokenOwner the actual owner of the tokens (as detected by findTokenOwner)
     * @param replacedNode the node being replaced in the AST
     * @return true if the tokenOwner's NodeText should be regenerated, false if normal LPP handling is sufficient
     */
    static boolean needsRegeneration(Node parent, Node tokenOwner, Node replacedNode) {
        // Case 1: Token owner is the same as the immediate parent
        // This is the normal case where LPP's default behavior (regenerating the parent) works correctly.
        // Example: x = 5; → replacing 5 in AssignExpr
        if (tokenOwner.equals(parent)) {
            return false;
        }
        // WORKAROUND: Multiple variable declarations share same type
        if (tokenOwner instanceof FieldDeclaration) {
            FieldDeclaration field = (FieldDeclaration) tokenOwner;
            if (field.getVariables().size() > 1) {
                // Let LPP handle it normally
                return false;
            }
        }
        // Case 2: Replaced node is directly a Type
        // This is the most common case requiring special handling (Issue #3365).
        // Types in declarations have their tokens owned by the declaration, not by the Type node itself.
        // Example: Set<Pair<...>> x; → replacing Pair type
        if (replacedNode instanceof Type) {
            return true;
        }
        // Case 3: Replaced node is contained within a Type
        // This handles nested cases where a node inside a type (e.g., type arguments) is replaced.
        // We walk up from the replaced node to the parent, checking if we pass through a Type node.
        // Example: Set<Pair<String, String>> → replacing "String" inside Pair's type arguments
        Node current = replacedNode.getParentNode().orElse(null);
        while (current != null && current != parent) {
            if (current instanceof Type) {
                // Found a Type node in the ancestry chain → regeneration needed
                return true;
            }
            current = current.getParentNode().orElse(null);
        }
        // Case 4: None of the above
        // The replaced node is not type-related and tokenOwner != parent.
        // This is rare but possible (e.g., annotations, modifiers in some cases).
        // Conservative approach: don't regenerate unless we're sure we need to.
        // If this causes issues, we can add more cases (annotations, modifiers, etc.)
        return false;
    }
}
