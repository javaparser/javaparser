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
package org.apache.commons.math3.exception.util;

import java.util.Locale;

/**
 * Dummy implementation of the {@link Localizable} interface, without localization.
 *
 * @since 2.2
 */
public class DummyLocalizable implements Localizable {

    /** Serializable version identifier. */
    private static final long serialVersionUID = 8843275624471387299L;

    /** Source string. */
    private final String source;

    /** Simple constructor.
     * @param source source text
     */
    public DummyLocalizable(final String source) {
        this.source = source;
    }

    /** {@inheritDoc} */
    public String getSourceString() {
        return source;
    }

    /** {@inheritDoc} */
    public String getLocalizedString(Locale locale) {
        return source;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return source;
    }

}
