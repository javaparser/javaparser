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

import minicdj.collision.Vector3d;

/**
 * Represents a definite collision that has occured.
 * 
 * @author Filip Pizlo
 */
/*@javax.safetycritical.annotate.Scope("cdx.CollisionDetectorHandler")*/
class Collision {
    /** The aircraft that were involved. */
    // private ArrayList aircraft;

    private Aircraft _one, _two;

    /** The location where the collision happened. */
    private Vector3d location;

    /** Construct a Collision with a given set of aircraft and a location. */
    /*	public Collision(List aircraft, Vector3d location) {
    		this.aircraft = new ArrayList(aircraft);
    		Collections.sort(this.aircraft);
    		this.location = location;
    	} */

    /** Construct a Coollision with two aircraft an a location. */
    public Collision(Aircraft one, Aircraft two, Vector3d location) {
        /*	aircraft = new ArrayList();
        	aircraft.add(one);
        	aircraft.add(two); 
        	Collections.sort(aircraft); */
        this.location = location;
        _one = one;
        _two = two;
    }

    public boolean hasAircraft(Aircraft a) {
        if (_one.equals(a)) return true;
        if (_two.equals(a)) return true;
        return false;
    }

    public Aircraft first() {
        return _one;
    }

    public Aircraft second() {
        return _two;
    }

    /*public int aircrafts() {
      return aircraft.size();
    } */

    /** Returns the list of aircraft involved. You are not to modify this list. */
    // public ArrayList getAircraftInvolved() { return aircraft; }

    /** Returns the location of the collision. You are not to modify this location. */
    public Vector3d getLocation() {
        return location;
    }

    /** Returns a hash code for this object. It is based on the hash codes of the aircraft. */

    public int hashCode() {
        int ret = 0;
        /*for (Iterator iter = aircraft.iterator(); iter.hasNext();) 
        	ret += ((Aircraft) iter.next()).hashCode(); */
        ret += _one.hashCode();
        ret += _two.hashCode();
        return ret;
    }

    /** Determines collision equality. Two collisions are equal if they have the same aircraft. */

    public boolean equals(Object _other) {
        if (_other == this) return true;
        if (!(_other instanceof Collision)) return false;
        Collision other = (Collision) _other;
        /*ArrayList a = getAircraftInvolved();
        ArrayList b = other.getAircraftInvolved();
        if (a.size() != b.size()) return false;
        Iterator ai = a.iterator();
        Iterator bi = b.iterator();
        while (ai.hasNext()) 
        	if (!ai.next().equals(bi.next())) return false; */
        // if ((other.hasAircraft(_one)) && (other.hasAircraft(_two))) return true;
        if (_one != other._one) return false;
        if (_two != other._two) return false;
        return true;
    }

    /** Returns a helpful description of this object. */

    public String toString() {
        StringBuffer buf = new StringBuffer("Collision between ");
        buf.append(_one.toString() + ", " + _two.toString());
        buf.append(" at ");
        buf.append(location.toString());
        return buf.toString();
    }
}
