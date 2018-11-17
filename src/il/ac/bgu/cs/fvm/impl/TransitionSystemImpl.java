package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder;
import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.*;

public class TransitionSystemImpl<STATE,ACTION,ATOMIC_PROPOSITION> implements TransitionSystem {

    private String name;
    private Set<ACTION> actions;
    private Set<STATE> states;
    private Set<STATE> initials;
    private Set<Transition> transitions;
    private Set<ATOMIC_PROPOSITION> aps;
    private Map<STATE, Set<ATOMIC_PROPOSITION>> labels;

    public TransitionSystemImpl(){
        actions = new HashSet<>();
        states = new HashSet<>();
        initials = new HashSet<>();
        transitions = new HashSet<>();
        aps = new HashSet<>();
        labels = new HashMap<>();
    }


    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public void setName(String name) {
        this.name= name;
    }

    @Override
    public void addAction(Object anAction) {
        actions.add((ACTION)anAction);
    }

    @Override
    public void setInitial(Object aState, boolean isInitial) throws StateNotFoundException {
        if (states.contains(aState)){
            if (initials.contains(aState) && !isInitial) {
                initials.remove((STATE) aState);
            }
            if (!initials.contains(aState) && isInitial) {
                initials.add((STATE) aState);
            }
        }
        else
            throw new StateNotFoundException("ERROR: setInitial function");
    }

    @Override
    public void addState(Object o) {
        states.add((STATE) o);

        Set<ATOMIC_PROPOSITION> s_labels = new HashSet<>();
        labels.put((STATE)o, s_labels);
    }

    @Override
    public void addTransition(Transition t) throws InvalidTransitionException {
        if (states.contains(t.getFrom()) && states.contains(t.getTo()) && actions.contains(t.getAction())) {
            transitions.add(t);
        }
        else
            throw new InvalidTransitionException(t);
    }

    @Override
    public Set getActions() {
        Set<ACTION> clonedActions = new HashSet<>(actions);
        return  clonedActions;
    }

    @Override
    public void addAtomicProposition(Object p) {
        aps.add((ATOMIC_PROPOSITION) p);
    }

    @Override
    public Set getAtomicPropositions() {
        return aps;
    }

    @Override
    public void addToLabel(Object s, Object l) throws FVMException {
        if (!aps.contains((ATOMIC_PROPOSITION)l))
            throw new FVMException("ERROR: the label isn't in the atomic proposition set");
        if (!states.contains((STATE)s))
            throw new StateNotFoundException("ERROR: state s isn't in states set");

        // add l to set of labels of s state.
        labels.get((STATE)s).add((ATOMIC_PROPOSITION)l);
    }

    @Override
    public Set getLabel(Object s) {
        if (!states.contains((STATE)s))
            throw new StateNotFoundException("ERROR: state s isn't in states set");
        return labels.get((STATE)s);
    }

    @Override
    public Set getInitialStates() {
        return initials;
    }

    @Override
    public Map getLabelingFunction() {
        return labels;
    }

    @Override
    public Set getStates() {
        return states;
    }

    @Override
    public Set<Transition> getTransitions() {
        return transitions;
    }

    @Override
    public void removeAction(Object o) throws DeletionOfAttachedActionException {
        for ( Transition tran: transitions ) {
            if (tran.getAction().equals((ACTION)o))
                throw new DeletionOfAttachedActionException((ACTION)o, TransitionSystemPart.ACTIONS);
        }

        actions.remove((ACTION)o);
    }

    @Override
    public void removeAtomicProposition(Object p) throws DeletionOfAttachedAtomicPropositionException {
        for (  Set<ATOMIC_PROPOSITION> s_labels: labels.values() ) {
            if (s_labels.contains((ATOMIC_PROPOSITION) p))
                throw new DeletionOfAttachedAtomicPropositionException((ATOMIC_PROPOSITION)p, TransitionSystemPart.ATOMIC_PROPOSITIONS);
        }

        aps.remove((ATOMIC_PROPOSITION) p);
    }

    @Override
    public void removeLabel(Object s, Object l) {
        labels.get((STATE)s).remove((ATOMIC_PROPOSITION)l);
    }

    @Override
    public void removeState(Object o) throws DeletionOfAttachedStateException {

        for (Transition tran : transitions){
            if (tran.getFrom().equals((STATE)o) || tran.getTo().equals((STATE)o)){
                throw new DeletionOfAttachedStateException((STATE)o, TransitionSystemPart.STATES);
            }
        }
        if( labels.keySet().contains((STATE)o) && !labels.get((STATE)o).isEmpty()) {
            throw new DeletionOfAttachedStateException((STATE)o, TransitionSystemPart.STATES);
        }
        if( initials.contains((STATE)o) ) {
            throw new DeletionOfAttachedStateException((STATE)o, TransitionSystemPart.STATES);
        }

        labels.remove((STATE)o);
        states.remove((STATE)o);
    }

    @Override
    public void removeTransition(Transition t) {
        transitions.remove(t);
    }
}
