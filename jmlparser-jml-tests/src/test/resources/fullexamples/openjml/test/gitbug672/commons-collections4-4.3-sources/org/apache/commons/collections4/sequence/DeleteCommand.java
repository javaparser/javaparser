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

/**
 * Command representing the deletion of one object of the first sequence.
 * <p>
 * When one object of the first sequence has no corresponding object in the
 * second sequence at the right place, the {@link EditScript edit script}
 * transforming the first sequence into the second sequence uses an instance of
 * this class to represent the deletion of this object. The objects embedded in
 * these type of commands always come from the first sequence.
 *
 * @see SequencesComparator
 * @see EditScript
 *
 * @since 4.0
 */
public class DeleteCommand<T> extends EditCommand<T> {

    /**
     * Simple constructor. Creates a new instance of {@link DeleteCommand}.
     *
     * @param object  the object of the first sequence that should be deleted
     */
    public DeleteCommand(final T object) {
        super(object);
    }

    /**
     * Accept a visitor. When a <code>DeleteCommand</code> accepts a visitor, it calls
     * its {@link CommandVisitor#visitDeleteCommand visitDeleteCommand} method.
     *
     * @param visitor  the visitor to be accepted
     */
    @Override
    public void accept(final CommandVisitor<T> visitor) {
        visitor.visitDeleteCommand(getObject());
    }
}
