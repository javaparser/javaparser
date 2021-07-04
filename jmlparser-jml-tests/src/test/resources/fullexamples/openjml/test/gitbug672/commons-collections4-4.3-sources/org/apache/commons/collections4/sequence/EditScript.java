/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.collections4.sequence;

import java.util.ArrayList;
import java.util.List;

/**
 * This class gathers all the {@link EditCommand commands} needed to transform
 * one objects sequence into another objects sequence.
 * <p>
 * An edit script is the most general view of the differences between two
 * sequences. It is built as the result of the comparison between two sequences
 * by the {@link SequencesComparator SequencesComparator} class. The user can
 * walk through it using the <em>visitor</em> design pattern.
 * <p>
 * It is guaranteed that the objects embedded in the {@link InsertCommand insert
 * commands} come from the second sequence and that the objects embedded in
 * either the {@link DeleteCommand delete commands} or {@link KeepCommand keep
 * commands} come from the first sequence. This can be important if subclassing
 * is used for some elements in the first sequence and the <code>equals</code>
 * method is specialized.
 *
 * @see SequencesComparator
 * @see EditCommand
 * @see CommandVisitor
 * @see ReplacementsHandler
 *
 * @since 4.0
 */
public class EditScript<T> {

    /** Container for the commands. */
    private final List<EditCommand<T>> commands;

    /** Length of the longest common subsequence. */
    private int lcsLength;

    /** Number of modifications. */
    private int modifications;

    /**
     * Simple constructor. Creates a new empty script.
     */
    public EditScript() {
        commands = new ArrayList<>();
        lcsLength = 0;
        modifications = 0;
    }

    /**
     * Add a keep command to the script.
     *
     * @param command  command to add
     */
    public void append(final KeepCommand<T> command) {
        commands.add(command);
        ++lcsLength;
    }

    /**
     * Add an insert command to the script.
     *
     * @param command  command to add
     */
    public void append(final InsertCommand<T> command) {
        commands.add(command);
        ++modifications;
    }

    /**
     * Add a delete command to the script.
     *
     * @param command  command to add
     */
    public void append(final DeleteCommand<T> command) {
        commands.add(command);
        ++modifications;
    }

    /**
     * Visit the script. The script implements the <em>visitor</em> design
     * pattern, this method is the entry point to which the user supplies its
     * own visitor, the script will be responsible to drive it through the
     * commands in order and call the appropriate method as each command is
     * encountered.
     *
     * @param visitor  the visitor that will visit all commands in turn
     */
    public void visit(final CommandVisitor<T> visitor) {
        for (final EditCommand<T> command : commands) {
            command.accept(visitor);
        }
    }

    /**
     * Get the length of the Longest Common Subsequence (LCS). The length of the
     * longest common subsequence is the number of {@link KeepCommand keep
     * commands} in the script.
     *
     * @return length of the Longest Common Subsequence
     */
    public int getLCSLength() {
        return lcsLength;
    }

    /**
     * Get the number of effective modifications. The number of effective
     * modification is the number of {@link DeleteCommand delete} and
     * {@link InsertCommand insert} commands in the script.
     *
     * @return number of effective modifications
     */
    public int getModifications() {
        return modifications;
    }

}
