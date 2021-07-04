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
 * This package contains implementations of the {@link java.util.Map Map},
 * {@link org.apache.commons.collections4.IterableMap IterableMap},
 * {@link org.apache.commons.collections4.OrderedMap OrderedMap} and
 * {@link java.util.SortedMap SortedMap} interfaces.
 * A Map provides a lookup from a key to a value.
 * A number of implementations also support the new MapIterator interface that enables
 * simple iteration of map keys and values.
 * <p>
 * The following implementations are provided:
 * <ul>
 *   <li>CaseInsensitiveMap - map that compares keys in a case insensitive way
 *   <li>CompositeMap - map that combines multiple maps into a single view
 *   <li>HashedMap - general purpose HashMap replacement supporting MapIterator
 *   <li>Flat3Map - designed for good performance at size 3 or less
 *   <li>LinkedMap - a hash map that maintains insertion order, supporting OrderedMapIterator
 *   <li>LRUMap - a hash map that maintains a maximum size by removing the least recently used entries
 *   <li>MultiKeyMap - map that provides special methods for using more than one key to access the value
 *   <li>ReferenceMap - allows the garbage collector to collect keys and values using equals() for comparison
 *   <li>ReferenceIdentityMap - allows the garbage collector to collect keys and values using == for comparison
 *   <li>SingletonMap - a fully featured map to hold one key-value pair
 *   <li>StaticBucketMap - internally synchronized and designed for thread-contentious environments
 * </ul>
 * <p>
 * The following decorators are provided:
 * <ul>
 *   <li>Unmodifiable - ensures the collection cannot be altered
 *   <li>Predicated - ensures that only elements that are valid according to a predicate can be added
 *   <li>Transformed - transforms each element added
 *   <li>FixedSize - ensures that the size of the map cannot change
 *   <li>Defaulted - provides default values for non-existing keys
 *   <li>Lazy - creates objects in the map on demand
 *   <li>ListOrdered - ensures that insertion order is retained
 * </ul>
 *
 */
package org.apache.commons.collections4.map;

