// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package geometry;

import java.util.*;

import geometry.routes.*;
import geometry.trajectory.*;


public class Factory
{

    /*@ public instance invariant routes != null;
      @ public instance invariant (\forall int i; 0<=i && i<routes.length;  
      @          routes[i] != null && 
      @          (\exists int j; j>=0 && j<routeToSegments.concrete_map.length;
      @              routeToSegments.concrete_map[j][0] == routes[i] &&
      @              routeToSegments.concrete_map[j][1] instanceof Object[]));
      @*/

    /*@ public instance invariant
      @ (\forall int i; i>=0 && i<routeToSegments.concrete_map.length; 
      @                 routeToSegments.concrete_map[i].length == 2) &&
      @ \nonnullelements(routeToSegments.concrete_map) && 
      @ (\forall int i,j; routeToSegments.concrete_map[j][0]==routeToSegments.concrete_map[i][0];
      @                   i==j);
      @   public instance invariant
      @      (\forall List li ; li != null;
      @              (\forall int i; li.list.length > i) && li.end >= 0);
      @*/

    private LinkedHashMap routeToSegments = null;	
    
    Object[][] dummy;

    private Object[] routes;
    private Factory(Object[] routes) { this.routes = routes; }


    /*@ public normal_behavior
      @   requires \is_initialized(java.util.ArrayList) &&
      @            \is_initialized(java.util.LinkedList) &&
      @            \is_initialized(java.util.AbstractSequentialList) &&
      @            \is_initialized(java.util.AbstractList) &&
      @            \is_initialized(java.util.List) &&
      @            \is_initialized(java.util.Collection);
      @   requires segments != null && l != null && segments.length >= 0;
      @   {|
      @       requires segments != l.list;
      @       ensures (\forall int i; i>0 && i<=segments.length; 
      @                l.list[l.end-i] == 
      @                segments[segments.length-i]);
      @       assignable l.end, 
      @                  l.list[l.end .. l.end+segments.length-1];
      @     also
      @       assignable l.list;
      @       ensures true; //to prove just termination
      @   |}
      @*/
    public void copyArrayToList(Object[] segments, LinkedList l){
	int j=0, sz=segments.length;
	boolean dummy;
	/*@ maintaining (\forall int k; k>0 && k<=j; 
	  @              l.list[l.end-k] == segments[j-k]) && j >= 0 &&
	  @              (\forall int i; l.list.length > i) && l.end >= 0 &&
	  @              j<=sz;
	  @ decreases sz-j; 
	  @ assignable j, l.list[l.end .. l.end+segments.length-1], 
	  @            l.end;
	  @*/
	while(j<sz && j>=0){
	    Object o = segments[j];
	    try{
		dummy = l.add(o);
	    }catch(Exception e){}
	    j++;
	}
    }
    
    
    /*@ public normal_behavior
      @   requires routeStart <= routeEnd;
      @   requires 0 <= routeStart;
      @   requires 0 <= routeEnd;
      @   requires routeEnd < routes.length;
      @   requires routeStart < routes.length;
      @   requires routeToSegments != null && routes != null;
      @   requires \is_initialized(java.util.ArrayList) &&
      @            \is_initialized(java.util.LinkedList) &&
      @            \is_initialized(java.util.HashMap) &&
      @            \is_initialized(java.util.LinkedHashMap) &&
      @            \is_initialized(java.util.Map) &&
      @            \is_initialized(java.util.AbstractMap)  &&
      @            \is_initialized(java.util.AbstractSequentialList) &&
      @            \is_initialized(java.util.AbstractList) &&
      @            \is_initialized(java.util.List);
      @*/
    public /*@ pure@*/ List getSegments(int routeStart, int routeEnd) {
	LinkedList l = new LinkedList();
	int i = routeStart;
	int index = routeStart;
	/*@ //maintaining (\forall int j; j>=routeStart && j<i; 
	    //              (\exists SegmentList seg; 
	    //		   seg == routeToSegments.get(routes.get(j)) && 
	    //		   (\forall int k; k>=0 && k<seg.size(); 
	    //		   l.contains(seg.get(k)))));
	  @ maintaining i >= routeStart;
	  @ decreases routeEnd-i+1; 
	  @ assignable i;
	  @*/
	while(i<=routeEnd && i>=routeStart) {
	    index = i;
	    Object route = routes[index];
	    Object[] segments = (Object[]) routeToSegments.get(route);
	    copyArrayToList(segments, l);
	    i++;
	}
	return l;
    }

}
