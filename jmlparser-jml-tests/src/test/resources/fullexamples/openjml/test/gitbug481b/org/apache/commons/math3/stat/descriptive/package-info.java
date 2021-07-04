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
 *
 *        Generic univariate summary statistic objects.
 *
 *        <h3>UnivariateStatistic API Usage Examples:</h3>
 *
 *        <h4>UnivariateStatistic:</h4>
 *        <code>/&lowast; evaluation approach &lowast;/<br/>
 *          double[] values = new double[] { 1, 2, 3, 4, 5 };<br/>
 *          <span style="font-weight: bold;">UnivariateStatistic stat = new Mean();</span><br/>
 *          out.println("mean = " + <span style="font-weight: bold;">stat.evaluate(values)</span>);<br/>
 *        </code>
 *
 *        <h4>StorelessUnivariateStatistic:</h4>
 *        <code>/&lowast; incremental approach &lowast;/<br/>
 *          double[] values = new double[] { 1, 2, 3, 4, 5 };<br/>
 *          <span style="font-weight: bold;">StorelessUnivariateStatistic stat = new Mean();</span><br/>
 *          out.println("mean before adding a value is NaN = " + <span style="font-weight: bold;">stat.getResult()</span>);<br/>
 *          for (int i = 0; i &lt; values.length; i++) {<br/>
 *            &nbsp;&nbsp;&nbsp; <span style="font-weight: bold;">stat.increment(values[i]);</span><br/>
 *            &nbsp;&nbsp;&nbsp; out.println("current mean = " + <span style="font-weight: bold;">stat2.getResult()</span>);<br/>
 *          }<br/>
 *          <span style="font-weight: bold;"> stat.clear();</span><br/>
 *          out.println("mean after clear is NaN = " + <span style="font-weight: bold;">stat.getResult()</span>);
 *        </code>
 *
 */
package org.apache.commons.math3.stat.descriptive;
