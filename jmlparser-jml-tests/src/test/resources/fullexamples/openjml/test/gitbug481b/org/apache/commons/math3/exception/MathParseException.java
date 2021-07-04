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
package org.apache.commons.math3.exception;

import org.apache.commons.math3.exception.util.ExceptionContextProvider;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Class to signal parse failures.
 *
 * @since 2.2
 */
public class MathParseException extends MathIllegalStateException
    implements ExceptionContextProvider {
    /** Serializable version Id. */
    private static final long serialVersionUID = -6024911025449780478L;

    /**
     * @param wrong Bad string representation of the object.
     * @param position Index, in the {@code wrong} string, that caused the
     * parsing to fail.
     * @param type Class of the object supposedly represented by the
     * {@code wrong} string.
     */
    public MathParseException(String wrong,
                              int position,
                              Class<?> type) {
        getContext().addMessage(LocalizedFormats.CANNOT_PARSE_AS_TYPE,
                                wrong, Integer.valueOf(position), type.getName());
    }

    /**
     * @param wrong Bad string representation of the object.
     * @param position Index, in the {@code wrong} string, that caused the
     * parsing to fail.
     */
    public MathParseException(String wrong,
                              int position) {
        getContext().addMessage(LocalizedFormats.CANNOT_PARSE,
                                wrong, Integer.valueOf(position));
    }
}
