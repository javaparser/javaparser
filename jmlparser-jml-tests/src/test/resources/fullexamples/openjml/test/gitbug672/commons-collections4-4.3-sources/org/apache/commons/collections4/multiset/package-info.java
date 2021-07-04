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
 * This package contains implementations of the
 * {@link org.apache.commons.collections4.MultiSet MultiSet} interface.
 * A multiset stores an object and a count of the number of occurrences of the object.
 * <p>
 * The following implementations are provided in the package:
 * <ul>
 *   <li>HashMultiSet - implementation that uses a HashMap to store the data
 * </ul>
 * <p>
 * The following decorators are provided in the package:
 * <ul>
 *   <li>Predicated   - ensures that only elements that are valid according to a predicate can be added
 *   <li>Synchronized - synchronizes method access for multi-threaded environments
 *   <li>Unmodifiable - ensures the multiset cannot be altered
 * </ul>
 *
 */
package org.apache.commons.collections4.multiset;
