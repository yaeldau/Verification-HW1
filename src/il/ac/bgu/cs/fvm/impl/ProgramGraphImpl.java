package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.*;

public class ProgramGraphImpl<L, A> implements ProgramGraph {

    String name;
    Set<List<String>> initVars;
    Set<L> locs;
    Set<L> initLocs;
    Set<PGTransition> trans;

    public ProgramGraphImpl(){
        name = "";
        initVars = new HashSet<>();
        locs = new HashSet<>();
        initLocs = new HashSet<>();
        trans = new HashSet<>();
    }

    @Override
    public void addInitalization(List init) {
        initVars.add(init);
    }

    @Override
    public void setInitial(Object location, boolean isInitial) {
        if (locs.contains(location)){
            if (initLocs.contains(location) && !isInitial) {
                initLocs.remove((L) location);
            }
            if (!initLocs.contains(location) && isInitial) {
                initLocs.add((L) location);
            }
        }
        else
            throw new IllegalArgumentException("location is not a location in pg");
    }

    @Override
    public void addLocation(Object o) {
        locs.add((L) o);
    }

    @Override
    public void addTransition(PGTransition t) {
        if (locs.contains(t.getFrom()) && locs.contains(t.getTo()) ) {
            trans.add(t);
        }
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return initVars;
    }

    @Override
    public Set getInitialLocations() {
        return initLocs;
    }

    @Override
    public Set getLocations() {
        return locs;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition> getTransitions() {
        return trans;
    }

    @Override
    public void removeLocation(Object o) {
        for(PGTransition t : trans){
            if (t.getFrom().equals(o) || t.getTo().equals(o)){
                removeTransition(t);
            }
        }
        locs.remove((L)o);
    }

    @Override
    public void removeTransition(PGTransition t) {
        trans.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
