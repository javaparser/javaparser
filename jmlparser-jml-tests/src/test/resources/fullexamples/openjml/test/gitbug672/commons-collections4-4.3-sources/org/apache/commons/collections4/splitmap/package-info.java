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
/**
 * The "split map" concept is that of an object that implements
 * the {@link org.apache.commons.collections4.Put Put} and
 * {@link org.apache.commons.collections4.Get Get} interfaces,
 * with <i>differing</i> generic types. This is like a pre-generics
 * {@link java.util.Map Map} whose input key/value constraints are
 * different than its output key/value constraints.  While it would
 * be possible to declare a "split map" with matching input/output
 * key/value constraints, this would be a {@link java.util.Map Map}
 * and would therefore make little sense (any Commons Collections
 * {@link java.util.Map Map} implementation will also implement
 * {@link org.apache.commons.collections4.Put Put} and
 * {@link org.apache.commons.collections4.Get Get} with matching
 * generic parameters).
 * <p>
 * The following decorators are provided:
 * <ul>
 *   <li>Transformed - transforms each element added
 * </ul>
 *
 */
package org.apache.commons.collections4.splitmap;
