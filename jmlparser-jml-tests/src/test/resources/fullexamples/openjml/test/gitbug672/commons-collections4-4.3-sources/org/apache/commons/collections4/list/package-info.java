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
 * This package contains implementations of the {@link java.util.List List} interface.
 * <p>
 * The following implementations are provided in the package:
 * <ul>
 *   <li>TreeList - a list that is optimised for insertions and removals at any index in the list</li>
 *   <li>CursorableLinkedList - a list that can be modified while the listIterator (cursor) is being used</li>
 *   <li>NodeCachingLinkedList - a linked list that caches the storage nodes for a performance gain</li>
 * </ul>
 * <p>
 * The following decorators are provided in the package:
 * <ul>
 *   <li>Unmodifiable - ensures the collection cannot be altered</li>
 *   <li>Predicated - ensures that only elements that are valid according to a predicate can be added</li>
 *   <li>Transformed - transforms each element added</li>
 *   <li>FixedSize - ensures that the size of the list cannot change</li>
 *   <li>Lazy - creates objects in the list on demand</li>
 *   <li>Growth - grows the list instead of erroring when set/add used with index beyond the list size</li>
 *   <li>SetUnique - a list that avoids duplicate entries like a Set</li>
 * </ul>
 *
 */
package org.apache.commons.collections4.list;
