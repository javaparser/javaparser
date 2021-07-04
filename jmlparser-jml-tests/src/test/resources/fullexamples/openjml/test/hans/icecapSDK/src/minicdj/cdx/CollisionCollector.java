/**
 *  This file is part of miniCDx benchmark of oSCJ.
 *
 *   miniCDx is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   miniCDx is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with miniCDx.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *   Copyright 2009, 2010 
 *   @authors  Daniel Tang, Ales Plsek
 *
 *   See: http://sss.cs.purdue.edu/projects/oscj/
 */
package minicdj.cdx;

import minicdj.util.ArrayList;
import minicdj.util.HashSet;
import minicdj.util.List;

/**
 * Collects collisions in lists and then returns a list of collisions where no two are equal.
 * 
 * @author Filip Pizlo
 */
/*@javax.safetycritical.annotate.Scope("cdx.CollisionDetectorHandler")*/
public class CollisionCollector {
    /** A hash set of collisions. */
    private HashSet collisions = new HashSet();

    /** Add some collisions. */
    public void addCollisions(List collisions) {
    // this.collisions.addAll(collisions);
    }

    /** Get the list of collisions. */
    public ArrayList getCollisions() {
        return new ArrayList(collisions);
    }
}
