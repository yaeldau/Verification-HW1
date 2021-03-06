package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.*;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.CollectionHelper;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

import java.io.*;
import java.util.*;


/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        TransitionSystem ts = new TransitionSystemImpl<S, A, P>();
        return ts;
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {

        if (ts.getInitialStates().size() > 1)
            return false;

        Set<Pair<S, A>> fromAndAction = new HashSet<>();
        for ( Transition tran : ts.getTransitions()){
            Pair<S, A> p = new Pair(tran.getFrom(), tran.getAction());
            if (fromAndAction.contains(p)) {
                return false;
            }
            fromAndAction.add(p);
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1)
            return false;

        Map<S, Set<P>> fromAndToTag = new HashMap<>();
        for ( Transition tran : ts.getTransitions()){
            Set<P> aps = ts.getLabelingFunction().get(tran.getTo());
            if (fromAndToTag.get(tran.getFrom()) != null){
                if (fromAndToTag.get(tran.getFrom()).retainAll(aps) || aps.equals(fromAndToTag.get(tran.getFrom())))
                    return false;
            }
            else {
                fromAndToTag.put((S) tran.getFrom(), new HashSet<P>());
            }
            fromAndToTag.get(tran.getFrom()).addAll(aps);
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        while (e.size() > 2){
            if (!ts.getStates().contains(e.head()))
                throw new StateNotFoundException(e.head());
            if (!ts.getStates().contains(e.tail().tail().head()))
                throw new StateNotFoundException(e.tail().tail().head());
            if (!ts.getActions().contains(e.tail().head()))
                throw new ActionNotFoundException(e.tail().head());

            Transition t = new Transition(e.head(), e.tail().head(), e.tail().tail().head());
            if (!ts.getTransitions().contains(t))
                return false;
            e = e.tail().tail();
        }
        if (e.size() == 1){
            if (!ts.getStates().contains(e.head())) {
                return false;
            }
        }

        return true;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(!ts.getInitialStates().contains(e.head())){
            return false;
        }

        return isExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isStateTerminal(ts, e.last()) && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException((S)s);

        for (Transition tran : ts.getTransitions()){
            if (tran.getFrom().equals(s)){
                return false;
            }
        }

        return true;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> post = new HashSet<>();
        for (Transition tran : ts.getTransitions()){
            if (tran.getFrom().equals(s)){
                post.add((S)tran.getTo());
            }
        }

        return post;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> post = new HashSet<>();
        for (S s : c){
            post.addAll(post(ts, s));
        }

        return post;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> post = new HashSet<>();
        for (Transition tran : ts.getTransitions()){
            if (tran.getFrom().equals(s) && tran.getAction().equals(a)){
                post.add((S)tran.getTo());
            }
        }

        return post;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> post = new HashSet<>();
        for (S s : c){
            post.addAll(post(ts, s, a));
        }

        return post;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> pre = new HashSet<>();
        for (Transition tran : ts.getTransitions()){
            if (tran.getTo().equals(s)){
                pre.add((S)tran.getFrom());
            }
        }

        return pre;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> pre = new HashSet<>();
        for (S s : c){
            pre.addAll(pre(ts, s));
        }

        return pre;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> pre = new HashSet<>();
        for (Transition tran : ts.getTransitions()){
            if (tran.getTo().equals(s) && tran.getAction().equals(a)){
                pre.add((S)tran.getFrom());
            }
        }

        return pre;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> pre = new HashSet<>();
        for (S s : c){
            pre.addAll(pre(ts, s, a));
        }

        return pre;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reach = new HashSet<>();
        reach.addAll(ts.getInitialStates());

        Set<S> post;
        while (!reach.containsAll(post = post(ts, reach)) ){
            reach.addAll(post);
        }

        return reach;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        TransitionSystem ts = new TransitionSystemImpl();
        ts.addAllActions(ts1.getActions());
        ts.addAllActions(ts2.getActions());
        ts.addAllAtomicPropositions(ts1.getAtomicPropositions());
        ts.addAllAtomicPropositions(ts2.getAtomicPropositions());

        Set<Pair<S1, S2>> states = new HashSet<>();
        for (S1 s1 : ts1.getStates()) {
            for (S2 s2 : ts2.getStates()) {
                states.add(new Pair<>(s1, s2));
            }
        }
        ts.addAllStates(states);

        for (Pair<S1,S2> s : states){
            if (ts1.getInitialStates().contains(s.first) && ts2.getInitialStates().contains(s.second)) {
                ts.setInitial(s, true);
            }
        }


        for (Transition tran1 : ts1.getTransitions()){
            for(Pair<S1, S2> sFrom : states){
                if (tran1.getFrom().equals(sFrom.first)){
                    for(Pair<S1, S2> sTo : states) {
                        if (tran1.getTo().equals(sTo.first)) {
                            if (sFrom.second.equals(sTo.second)) {
                                ts.addTransition(new Transition(sFrom, tran1.getAction(), sTo));
                            }
                        }
                    }
                }
            }
        }
        for (Transition tran2 : ts2.getTransitions()){
            for(Pair<S1, S2> sFrom : states){
                if (tran2.getFrom().equals(sFrom.second)){
                    for(Pair<S1, S2> sTo : states) {
                        if (tran2.getTo().equals(sTo.second)) {
                            if (sFrom.first.equals(sTo.first)) {
                                ts.addTransition(new Transition(sFrom, tran2.getAction(), sTo));
                            }
                        }
                    }
                }
            }
        }

        Map<S1, Set<P>> labels1 = ts1.getLabelingFunction();
        for (S1 s1 : labels1.keySet()){
            for(Pair<S1,S2> s : states){
                if (s.first.equals(s1)){
                    for (P p : labels1.get(s.first)) {
                        ts.addToLabel(s, p);
                    }
                }
            }
        }
        Map<S2, Set<P>> labels2 = ts2.getLabelingFunction();
        for (S2 s2 : labels2.keySet()){
            for(Pair<S1,S2> s : states){
                if (s.second.equals(s2)){
                    for (P p : labels2.get(s.second)) {
                        ts.addToLabel(s, p);
                    }
                }
            }
        }

        return ts;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem ts = new TransitionSystemImpl();
        ts.addAllActions(ts1.getActions());
        ts.addAllActions(ts2.getActions());
        ts.addAllAtomicPropositions(ts1.getAtomicPropositions());
        ts.addAllAtomicPropositions(ts2.getAtomicPropositions());

        Set<Pair<S1, S2>> states = new HashSet<>();
        for (S1 s1 : ts1.getStates()) {
            for (S2 s2 : ts2.getStates()) {
                states.add(new Pair<>(s1, s2));
            }
        }
        ts.addAllStates(states);

        for (Pair<S1,S2> s : states){
            if (ts1.getInitialStates().contains(s.first) && ts2.getInitialStates().contains(s.second)) {
                ts.setInitial(s, true);
            }
        }


        Set<Transition> tsTrans = new HashSet<>();
        for (Transition tran1 : ts1.getTransitions()){
            if (!handShakingActions.contains(tran1.getAction())) {
                for (Pair<S1, S2> sFrom1 : states) {
                    if (tran1.getFrom().equals(sFrom1.first)) {
                        for (Pair<S1, S2> sTo : states) {
                            if (tran1.getTo().equals(sTo.first)) {
                                if (sFrom1.second.equals(sTo.second)) {
                                    Transition toAdd = new Transition<>(sFrom1, tran1.getAction(), sTo);
                                    ts.addTransition(toAdd);
                                    tsTrans.add(toAdd);
                                }
                            }
                        }
                    }
                }
            }
            else{
                for (Pair<S1, S2> sFrom1 : states) {
                    if (tran1.getFrom().equals(sFrom1.first)) {
                        for (Pair<S1, S2> sTo : states) {
                            if (tran1.getTo().equals(sTo.first)) {
                                if (ts2.getTransitions().contains(new Transition<>(sFrom1.second, tran1.getAction(), sTo.second))) {
                                    Transition toAdd = new Transition<>(sFrom1, tran1.getAction(), sTo);
                                    ts.addTransition(toAdd);
                                    tsTrans.add(toAdd);
                                }
                            }
                        }
                    }
                }
            }
        }
        for (Transition tran2 : ts2.getTransitions()){
            if (!handShakingActions.contains(tran2.getAction())) {
                for (Pair<S1, S2> sFrom : states) {
                    if (tran2.getFrom().equals(sFrom.second)) {
                        for (Pair<S1, S2> sTo : states) {
                            if (tran2.getTo().equals(sTo.second)) {
                                if (sFrom.first.equals(sTo.first)) {
                                    Transition toAdd = new Transition<>(sFrom, tran2.getAction(), sTo);
                                    ts.addTransition(toAdd);
                                    tsTrans.add(toAdd);
                                }
                            }
                        }
                    }
                }
            }
            else{
                for (Pair<S1, S2> sFrom2 : states) {
                    if (tran2.getFrom().equals(sFrom2.second)) {
                        for (Pair<S1, S2> sTo : states) {
                            if (tran2.getTo().equals(sTo.second)) {
                                if (ts1.getTransitions().contains(new Transition<>(sFrom2.first, tran2.getAction(), sTo.first))) {
                                    Transition toAdd = new Transition<>(sFrom2, tran2.getAction(), sTo);
                                    ts.addTransition(toAdd);
                                    tsTrans.add(toAdd);
                                }
                            }
                        }
                    }
                }
            }
        }


        Set<Pair<S1,S2>> newStates = reach(ts);
        for (Pair<S1,S2> s : states) {
            if (!newStates.contains(s)) {
                for (Transition t : tsTrans){
                    if (t.getFrom().equals(s) || t.getTo().equals(s)) {
                        ts.removeTransition(t);
                    }
                }
                ts.removeState(s);
            }
        }


        Map<S1, Set<P>> labels1 = ts1.getLabelingFunction();
        for (S1 s1 : labels1.keySet()){
            for(Pair<S1,S2> s : states){
                if (s.first.equals(s1)){
                    for (P p : labels1.get(s.first)) {
                        ts.addToLabel(s, p);
                    }
                }
            }
        }
        Map<S2, Set<P>> labels2 = ts2.getLabelingFunction();
        for (S2 s2 : labels2.keySet()){
            for(Pair<S1,S2> s : states){
                if (s.second.equals(s2)){
                    for (P p : labels2.get(s.second)) {
                        ts.addToLabel(s, p);
                    }
                }
            }
        }

        return ts;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        ProgramGraph pg = new ProgramGraphImpl();
        return pg;
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> pg = new ProgramGraphImpl<>();
        for(L1 l1 : pg1.getLocations()){
            for(L2 l2 : pg2.getLocations()) {
                pg.addLocation(new Pair<>(l1, l2));
            }
        }

        for( Pair<L1, L2> l : pg.getLocations()){
            if (pg1.getInitialLocations().contains(l.getFirst()) && pg2.getInitialLocations().contains(l.getSecond() )){
                pg.setInitial(l, true);
            }
        }


        for (List<String> l1 : pg1.getInitalizations()){
            for (List<String> l2 : pg2.getInitalizations()){
                List<String> l = new ArrayList<>(l1);
                l.addAll(l2);
                pg.addInitalization(l);
            }
        }


        for (PGTransition tran1 : pg1.getTransitions()){
            for(Pair<L1, L2> sFrom : pg.getLocations()){
                if (tran1.getFrom().equals(sFrom.first)){
                    for(Pair<L1, L2> sTo : pg.getLocations()) {
                        if (tran1.getTo().equals(sTo.first)) {
                            if (sFrom.second.equals(sTo.second)) {
                                pg.addTransition(new PGTransition(sFrom, tran1.getCondition(), tran1.getAction(), sTo));
                            }
                        }
                    }
                }
            }
        }
        for (PGTransition tran2 : pg2.getTransitions()){
            for(Pair<L1, L2> sFrom : pg.getLocations()){
                if (tran2.getFrom().equals(sFrom.second)){
                    for(Pair<L1, L2> sTo : pg.getLocations()) {
                        if (tran2.getTo().equals(sTo.second)) {
                            if (sFrom.first.equals(sTo.first)) {
                                pg.addTransition(new PGTransition(sFrom, tran2.getCondition(), tran2.getAction(), sTo));
                            }
                        }
                    }
                }
            }
        }

        return pg;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = new TransitionSystemImpl<>();

        // states
        Set<Pair<Map<String, Boolean>,Map<String, Boolean>>> states = new HashSet<>();
        Set<Pair<Map<String, Boolean>,Map<String, Boolean>>> inits = new HashSet<>();

        Set<Set<String>> powerSetRegs = Util.powerSet(c.getRegisterNames());
        Set<Set<String>> powerSetInputs = Util.powerSet(c.getInputPortNames());

        Set<Map<String, Boolean>> regsMaps = new HashSet<>();
        for (Set<String> regSet : powerSetRegs){
            Map<String, Boolean> regsMap = new HashMap<>();
            for (String reg : c.getRegisterNames()){
                if (regSet.contains(reg)){
                    regsMap.put(reg, true);
                }
                else{
                    regsMap.put(reg, false);
                }
            }
            regsMaps.add(regsMap);
        }

        Set<Map<String, Boolean>> inputsMaps = new HashSet<>();
        for (Set<String> inputSet : powerSetInputs){
            Map<String, Boolean> inputsMap = new HashMap<>();
            for (String input : c.getInputPortNames()){
                if (inputSet.contains(input)){
                    inputsMap.put(input, true);
                }
                else{
                    inputsMap.put(input, false);
                }
            }
            inputsMaps.add(inputsMap);
        }

        for (Map<String, Boolean> regsMap : regsMaps){
            for (Map<String, Boolean> inputsMap : inputsMaps){
                Pair<Map<String, Boolean>, Map<String, Boolean>> p = new Pair<>(inputsMap, regsMap);
                states.add(p);
                // inits
                if(!p.getSecond().values().contains(true)){
                    inits.add(p);
                }
            }
        }
        ts.addAllStates(states);
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> init : inits){
            ts.setInitial(init, true);
        }

        // act
        ts.addAllActions(inputsMaps);

        //trans
        Set<Transition<Pair<Map<String, Boolean>,Map<String, Boolean>>, Map<String, Boolean>>> trans = new HashSet<>();
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates()){
            for (Map<String, Boolean> act : ts.getActions()){
                Pair<Map<String, Boolean>, Map<String, Boolean>> to =  new Pair<>(act, c.updateRegisters(state.first, state.second));
                trans.add(new Transition<>(state, act, to));
            }

        }
        for(Transition t : trans){
            ts.addTransition(t);
        }


        Set<Pair<Map<String, Boolean>,Map<String, Boolean>>> newStates = reach(ts);
        for (Pair<Map<String, Boolean>,Map<String, Boolean>> s : states) {
            if (!newStates.contains(s)) {
                Set<Transition<Pair<Map<String, Boolean>,Map<String, Boolean>>, Map<String, Boolean>>> transToRemove = new HashSet<>();
                for (Transition t : trans){
                    if (t.getFrom().equals(s) || t.getTo().equals(s)) {
                        transToRemove.add(t);
                    }
                }
                for(Transition tToRemove : transToRemove){
                    ts.removeTransition(tToRemove);
                }
                ts.removeState(s);
            }
        }

        // aps
        for (String reg : c.getRegisterNames()) {
            ts.addAtomicProposition(reg);
        }
        for (String input : c.getInputPortNames()) {
            ts.addAtomicProposition(input);
        }
        for (String output : c.getOutputPortNames()) {
            ts.addAtomicProposition(output);
        }

        // labels
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates()){
            for (String input : state.first.keySet()){
                if (state.first.get(input)){
                    ts.addToLabel(state, input);
                }
            }
            for (String reg : state.second.keySet()){
                if (state.second.get(reg)){
                    ts.addToLabel(state, reg);
                }
            }
            Map<String, Boolean> outputs = c.computeOutputs(state.first, state.second);
            for (String output : outputs.keySet()){
                if (outputs.get(output)){
                    ts.addToLabel(state, output);
                }
            }
        }

        return ts;
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {

        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystemImpl<>();

        // actions
        for (PGTransition tran : pg.getTransitions()){
            ts.addAction((A)tran.getAction());
        }

        // locations
        //Set<Pair<L, Map<String, Object>>> states = new HashSet<>();

        Set<Map<String, Object>> evals = new HashSet<>();
        for (List<String> list : pg.getInitalizations()){
            Map<String, Object> map = new HashMap<>();
            for(String action : list) {
                map = ActionDef.effect(actionDefs, map, action);
            }
            evals.add(map);

        }
        if(evals.isEmpty()){
            evals.add(new HashMap<>());
        }

        for (L init : pg.getInitialLocations()){
            for ( Map<String, Object> eval : evals){

                Pair<L, Map<String, Object>> initState = new Pair<>(init, eval);
                //states.add(initState);
                ts.addState(initState);
                ts.setInitial(initState, true);
                // aps
                for (String key : eval.keySet()){
                    ts.addAtomicProposition(key + " = " + eval.get(key));
                }
            }
        }


        Queue<Pair<L, Map<String, Object>>> states = new LinkedList<>(ts.getStates());
        while (!states.isEmpty()){

            Pair<L, Map<String, Object>> state = states.poll();

            for (PGTransition<L,A> tran : pg.getTransitions()){
                if (state.first.equals(tran.getFrom()) && ConditionDef.evaluate(conditionDefs, state.second, tran.getCondition())) {
                    Map<String, Object> effect = ActionDef.effect(actionDefs, state.second, tran.getAction());
                    if (effect != null) {
                        Pair<L, Map<String, Object>> to = new Pair<>(tran.getTo(), effect);
                        if (!ts.getStates().contains(to)) {
                            ts.addState(to);
                            states.add(to);
                        }

                        // trans
                        if (ConditionDef.evaluate(conditionDefs, state.second, tran.getCondition())) {
                            ts.addTransition(new Transition<>(state, tran.getAction(), to));
                        }
                    }


                }
            }
        }

        Set<Pair<L, Map<String, Object>>> states1 = new HashSet<>(ts.getStates());
        Set<Pair<L, Map<String, Object>>> reach = reach(ts);
        for (Pair<L, Map<String, Object>> state : states1){
            if (!reach.contains(state)){
                ts.removeState(state);
            }
        }


        // labeling
        for (Pair<L, Map<String, Object>> state : ts.getStates()) {
            if (state.first instanceof ArrayList<?>) {
                for (L l : (ArrayList<L>) state.first) {
                    ts.addAtomicProposition(l.toString());
                    ts.addToLabel(state, l.toString());
                }
            } else {
                ts.addAtomicProposition(state.first.toString());
                ts.addToLabel(state, state.first.toString());
            }


            for (PGTransition tran : pg.getTransitions()){
                for (String key : state.second.keySet()) {
                    ts.addAtomicProposition(key + " = " + state.second.get(key));
                    ts.addToLabel(state, key + " = " + state.second.get(key));
                }
            }
        }


        return ts;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {

        ProgramGraph<List<L>,A> pg = new ProgramGraphImpl<>();

        // first pg
        ProgramGraph<L, A> pg1 = cs.getProgramGraphs().get(0);
        for (L locij : pg1.getLocations()){
            // locations
            List<L> newLoc = new ArrayList<>();
            newLoc.add(locij);
            pg.addLocation(newLoc);

            // init
            if (pg1.getInitialLocations().contains(locij)){
                pg.setInitial(newLoc, true);
            }
        }

        // trans
        for (PGTransition<L,A> tran : pg1.getTransitions()){
            PGTransition<List<L>, A> newTran = new PGTransition<>(
                    Arrays.asList(tran.getFrom()), tran.getCondition() ,tran.getAction(), Arrays.asList(tran.getTo()));
            pg.addTransition(newTran);
        }

        // initializations
        for (List<String> inits : pg1.getInitalizations()) {
            pg.addInitalization(inits);
        }

        // rest pg-s
        for (int i=1; i<cs.getProgramGraphs().size(); i++) {
            ProgramGraph<L, A> pgi = cs.getProgramGraphs().get(i);
            pg = addProgramGraphs(pg, pgi);
        }



        Set<ActionDef> actionDefs = new LinkedHashSet<>();
        actionDefs.add( new ParserBasedInterleavingActDef());
        actionDefs.add( new ParserBasedActDef());
        Set<ConditionDef> conditionDefs = new HashSet<>();
        conditionDefs.add(new ParserBasedCondDef());

        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts =
                transitionSystemFromProgramGraph(pg, actionDefs, conditionDefs);
        return ts;
    }

    private <L,A> ProgramGraph<List<L>, A> addProgramGraphs(ProgramGraph<List<L>, A> pgAll, ProgramGraph<L, A> pgi){
        ProgramGraph<List<L>, A> pg = createProgramGraph();
        // locations
        Set<List<L>> locations = new HashSet<>( pgAll.getLocations());
        for (List<L> locs : locations) {
            for (L locij : pgi.getLocations()) {
                List<L> newLoc = new ArrayList<>(locs);
                newLoc.add(locij);
                pg.addLocation(newLoc);

                // init
                if (pgi.getInitialLocations().contains(locij) && pgAll.getInitialLocations().contains(locs)) {
                    pg.setInitial(newLoc, true);
                }
            }
        }

        // trans
        ParserBasedInterleavingActDef parser = new ParserBasedInterleavingActDef();
        Set<PGTransition<List<L>, A>> transitions = new HashSet<>(pgAll.getTransitions());
        for (PGTransition<List<L>, A> pgTran : transitions) {
            if (!parser.isOneSidedAction(pgTran.getAction().toString())) {
                for (L loc : pgi.getLocations()) {
                    List<L> from = new ArrayList<>(pgTran.getFrom());
                    from.add(loc);
                    List<L> to = new ArrayList<>(pgTran.getTo());
                    to.add(loc);
                    PGTransition<List<L>, A> newTran = new PGTransition<>(
                            from, pgTran.getCondition(), pgTran.getAction(), to);
                    pg.addTransition(newTran);
                }
            }
        }

        for (PGTransition<L, A> pgiTran : pgi.getTransitions()) {
            if (!parser.isOneSidedAction(pgiTran.getAction().toString())) {
                for (List<L> loc : pgAll.getLocations()) {
                    List<L> from = new ArrayList<>(loc);
                    from.add(pgiTran.getFrom());
                    List<L> to = new ArrayList<>(loc);
                    to.add(pgiTran.getTo());
                    PGTransition<List<L>, A> newTran = new PGTransition<>(
                            from, pgiTran.getCondition(), pgiTran.getAction(), to);
                    pg.addTransition(newTran);
                }
            }
        }

        transitions = new HashSet<>(pgAll.getTransitions());
        for (PGTransition<List<L>, A> pgTran : transitions) {
            for (PGTransition<L, A> pgiTran : pgi.getTransitions()) {
                A act = getHandShakeAction(pgTran.getAction(), pgiTran.getAction(), parser);
                if( act != null) {
                    List<L> from = new ArrayList<>(pgTran.getFrom());
                    from.add(pgiTran.getFrom());
                    List<L> to = new ArrayList<>(pgTran.getTo());
                    to.add(pgiTran.getTo());
                    PGTransition<List<L>, A> newTran = new PGTransition<>(
                            from, mergeConditions(pgTran.getCondition(), pgiTran.getCondition()), act, to);
                    pg.addTransition(newTran);
                }
            }
        }

        // initializations
        Set<List<String>> inits =  new HashSet<>(pgAll.getInitalizations());
        for (List<String> pginits : inits) {
            for (List<String> pgiinits : pgi.getInitalizations()) {
                List<String> init = new ArrayList<>(pginits);
                init.addAll(pgiinits);
                pg.addInitalization(init);
            }
        }
        if (pgAll.getInitalizations().isEmpty()){
            for (List<String> init : pgi.getInitalizations()){
                pg.addInitalization(init);
            }
        }

        if (pgi.getInitalizations().isEmpty()){
            for (List<String> init : pgAll.getInitalizations()){
                pg.addInitalization(init);
            }
        }
        return pg;
    }

    private <A> A getHandShakeAction(A pgaction, A pgiaction, ParserBasedInterleavingActDef parser) {
        if (!(pgaction instanceof String) || !(pgiaction instanceof String))
            return null;
        if(!parser.isOneSidedAction(pgaction.toString()) || !parser.isOneSidedAction(pgiaction.toString()))
            return null;

        if (((String)pgaction).contains("?") && ((String)pgiaction).contains("!")){
            String pgchannel = ((String) pgaction).substring(0, ((String) pgaction).indexOf("?"));
            String pgichannel = ((String) pgiaction).substring(0, ((String) pgiaction).indexOf("!"));
            if(  pgchannel.equals(pgichannel))
                return (A)String.format("%s|%s", pgaction, pgiaction);
        }

        if (((String)pgaction).contains("!") && ((String)pgiaction).contains("?")){
            String pgchannel = ((String) pgaction).substring(0, ((String) pgaction).indexOf("!"));
            String pgichannel = ((String) pgiaction).substring(0, ((String) pgiaction).indexOf("?"));
            if ( pgchannel.equals(pgichannel)) {
                return (A)String.format("%s|%s", pgaction.toString(), pgiaction.toString());
            }
        }

        return null;
    }


    private String mergeConditions(String PGCondition, String PGiCondition) {
        if (PGCondition.length() == 0)
            return PGiCondition;
        if (PGiCondition.length() == 0)
            return PGCondition;
        return "(" + PGCondition + ") && (" + PGiCondition + ")";
    }


    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        return programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaFile(filename));
    }


    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        return programGraphFromNanoPromela(NanoPromelaFileReader.parseNanoPromelaStream(inputStream));
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        return programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaString(nanopromela));
    }














    final String LOC_EXIT = "";
    final String ACT_NOTHING = "";
    final String COND_TRUE = "";


    private ProgramGraph<String, String> programGraphFromNanoPromela(StmtContext nanopromela) throws Exception {
        ProgramGraph<String, String> pg = createProgramGraph();
        Map<String, Set<PGTransition<String, String>>> locsToTrans = new HashMap<>();
        sub(nanopromela, locsToTrans);

        // expand
        pg.addLocation(nanopromela.getText());
        Queue<String> locs = new LinkedList<>(pg.getLocations());
        while (!locs.isEmpty()) {
            String loc = locs.poll();
            if (!loc.equals(""))
                for (PGTransition<String, String> tran : locsToTrans.get(loc)) {
                    if (!pg.getLocations().contains(tran.getTo())) {
                        pg.addLocation(tran.getTo());
                        locs.add(tran.getTo());
                    }
                    pg.addTransition(tran);
                }
        }

        pg.setInitial(nanopromela.getText(), true);

        return pg;
    }



    private void sub(StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTrans) {
        if (subTrans.keySet().contains(stmt.getText())) { return; }

        Set<PGTransition<String, String>> trans = new HashSet<>();

        // atomic
        if (stmt.assstmt() != null || stmt.chanreadstmt() != null || stmt.chanwritestmt() != null
                || stmt.atomicstmt() != null || stmt.skipstmt() != null) {
            trans.add(new PGTransition<>(stmt.getText(), COND_TRUE, stmt.getText(), LOC_EXIT));
            subTrans.put(stmt.getText(), trans);
        }

        else if (stmt.ifstmt() != null) { ifSub(stmt, subTrans, trans); }

        else if (stmt.dostmt() != null) { doSub(stmt, subTrans); }

        else {  concatSub(stmt, subTrans); }
    }

    private void ifSub(StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTrans, Set<PGTransition<String, String>> trans) {
        for (OptionContext option : stmt.ifstmt().option()) {
            sub(option.stmt(), subTrans);
            for (PGTransition<String, String> tran : subTrans.get(option.stmt().getText())) {
                String cond = "(" + option.boolexpr().getText() + ") && (" + tran.getCondition() + ")";
                if (option.boolexpr().getText().equals(""))
                    cond = "(" + tran.getCondition() + ")";
                if (tran.getCondition().equals(""))
                    cond = "(" + option.boolexpr().getText() + ")";
                if (tran.getCondition().equals("") && option.boolexpr().getText().equals(""))
                    cond = "";
                trans.add(new PGTransition<>(stmt.getText(), cond, tran.getAction(), tran.getTo()));
            }
        }
        subTrans.put(stmt.getText(), trans);
    }

    private void doSub(StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTrans) {
        String falseCond = "";
        for (OptionContext option : stmt.dostmt().option()) {
            sub(option.stmt(), subTrans);
            String gi = option.boolexpr().getText();
            String notgi = "!(" + gi + ") && ";
            falseCond += notgi;
            doTran(subTrans, stmt.getText(), option.stmt().getText(), stmt.getText(), gi, new HashSet<>());
        }

        falseCond = "(" + falseCond.substring(0, falseCond.length() - 4) + ")";

        addTran(subTrans, new PGTransition<>(stmt.getText(), falseCond, ACT_NOTHING, LOC_EXIT));
    }

    private void concatSub(StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTrans) {
        StmtContext stmt1 = stmt.stmt(0);
        StmtContext stmt2 = stmt.stmt(1);
        sub(stmt1, subTrans);
        sub(stmt2, subTrans);
        concatinetionTran(subTrans, stmt.getText(), stmt1.getText(), stmt2.getText(), new HashSet<>());
    }

    private void addTran(Map<String, Set<PGTransition<String, String>>> subTrans,
                         PGTransition<String, String> tran) {
        if (!subTrans.containsKey(tran.getFrom()))
            subTrans.put(tran.getFrom(), new HashSet<>());
        Set<PGTransition<String, String>> transitions = subTrans.get(tran.getFrom());
        transitions.add(tran);
    }


    private void doTran(Map<String, Set<PGTransition<String, String>>> subTrans, String stmt,
                        String stmt1, String stmt2, String gi, Set<String> handled) {
        if (handled.contains(stmt1))
            return;
        handled.add(stmt1);
        for (PGTransition<String, String> tran : subTrans.get(stmt1)) {
            String cond = "(" + gi + ") && (" + tran.getCondition() + ")";
            if (gi.equals(""))
                cond = "(" + tran.getCondition() + ")";
            if (tran.getCondition().equals(""))
                cond = "(" + gi + ")";
            if (tran.getCondition().equals("") && gi.equals(""))
                cond = "";

            String to = tran.getTo() + ";" + stmt2;
            if ( tran.getTo().equals(""))
                to = stmt2;

            addTran(subTrans, new PGTransition<>(stmt, cond, tran.getAction(), to));
            if (!tran.getTo().isEmpty())
                doTran(subTrans, to, tran.getTo(), stmt2, COND_TRUE, handled);
        }
    }

    private void concatinetionTran(Map<String, Set<PGTransition<String, String>>> subTrans, String stmt,
                                   String stmt1, String stmt2, Set<String> handled) {
        if (handled.contains(stmt1))
            return;
        handled.add(stmt1);
        for (PGTransition<String, String> tran : subTrans.get(stmt1)) {
            String to = tran.getTo() + ";" + stmt2;
            if (tran.getTo().equals(""))
                to = stmt2;
            addTran(subTrans, new PGTransition<>(stmt, tran.getCondition(), tran.getAction(), to));
            if (!tran.getTo().isEmpty())
                concatinetionTran(subTrans, to, tran.getTo(), stmt2, handled);
        }
    }






    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<Sts, Saut>, A, Saut> tsProd = new TransitionSystemImpl();
        // actions
        tsProd.addAllActions(ts.getActions());
        // aps
        tsProd.addAllAtomicPropositions(aut.getTransitions().keySet());
        // states
        Set<Sts> S = ts.getStates();
        Set<Saut> Q = aut.getTransitions().keySet();
        (CollectionHelper.product(S,Q)).forEach(newState -> tsProd.addState(newState));
        // inits
        for (Sts sts: ts.getInitialStates()) {
            for (Saut saut : aut.getInitialStates()){
                for (Saut next: aut.nextStates(saut, ts.getLabel(sts))) {
                    tsProd.setInitial(new Pair<>(sts, next), true);
                }
            }
        }
        // labels
        for (Pair<Sts, Saut> p: tsProd.getStates()) {
            tsProd.addToLabel(p, p.second);
        }
        // trans
        for( Transition<Sts, A> tran : ts.getTransitions()){
            for (Saut saut : aut.getTransitions().keySet()) {
                Sts to2 = tran.getTo();
                Set<P> ls = ts.getLabel(to2);
                Set<Saut> nexts = aut.nextStates(saut, ls);
                if (nexts != null) {
                    for (Saut next : nexts) {
//                  for (Saut next : aut.nextStates(saut, ts.getLabel(tran.getTo()))) {
                        Pair<Sts, Saut> from = new Pair<>(tran.getFrom(), saut);
                        Pair<Sts, Saut> to = new Pair<>(tran.getTo(), next);
                        tsProd.addTransition(new Transition<>(from, tran.getAction(), to));
                    }
                }
            }
        }

        Set<Pair<Sts,Saut>> states = new HashSet<>(tsProd.getStates());
        Set<Transition<Pair<Sts,Saut>, A>> trans = new HashSet<>(tsProd.getTransitions());
        Set<Pair<Sts,Saut>> newStates = reach(tsProd);
        for (Pair<Sts,Saut> s : states) {
            if (!newStates.contains(s)) {
                for (Transition t : trans){
                    if (t.getFrom().equals(s) || t.getTo().equals(s)) {
                        tsProd.removeTransition(t);
                    }
                }
                tsProd.removeLabel(s, s.second);
                tsProd.removeState(s);
            }
        }

        Set<Saut> actualLabels = new HashSet<>();
        for(Pair<Sts,Saut> p : tsProd.getStates()){
            actualLabels.addAll(tsProd.getLabel(p));
        }
        Set<Saut> newLabels = new HashSet<>(tsProd.getAtomicPropositions());
        for(Saut ap : newLabels){
            if (!actualLabels.contains(ap)){
                tsProd.removeAtomicProposition(ap);
            }
        }

        return tsProd;
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        //1. build predicate
        //2. for-each all states
        //3.    labels(s) < !predicate
        //4.    cycle(S)
        //5.    if true -> return

        TransitionSystem<Pair<S, Saut>, A, Saut> tsProd = product(ts, aut);
        Set<Saut> predicate = new HashSet<>(aut.getAcceptingStates());
        for(Pair<S, Saut> s : tsProd.getStates()){
            // s satisfy the predicate:
            for (Saut l : tsProd.getLabel(s)){
                if (predicate.contains(l)){
                    // s is part of cycle:
                    List<S> cycle = new LinkedList<>();
                    boolean foundCycle = findPath(tsProd, s, s, cycle, new HashSet<>());
                    if (foundCycle) {
                        VerificationResult vf = new VerificationFailed();
                        List<S> prefix = new LinkedList<>();
                        for(Pair<S, Saut> init: tsProd.getInitialStates()){
                            if(findPath(tsProd, s, init, prefix, new HashSet<>())){
                                prefix.add(init.first);
                                Collections.reverse(prefix);
                                prefix.add(s.first);
                                ((VerificationFailed) vf).setPrefix(prefix);
                                break;
                            }
                        }

                        Collections.reverse(cycle);
                        cycle.add(s.first);
                        ((VerificationFailed) vf).setCycle(cycle);
                        return vf;
                    }
                }
            }

        }

        return new VerificationSucceeded<>();

    }

    private <S, Saut, A> boolean findPath (TransitionSystem<Pair<S, Saut>, A, Saut> tsProd,
                                           Pair<S, Saut> s, Pair<S, Saut> nextS, List<S> path, Set states){

        for(Pair<S, Saut> next : post(tsProd, nextS)){

            if ((next.first).equals(s.first)) {
//                path.add(s);
                return true;
            }
            if (!states.contains(next)){
                states.add(next);
                if (findPath(tsProd, s, next, path, states)){
                    path.add(next.first);
                    return true;
                }

            }
        }
        return false;
    }

    //------------------------------------------------------------------------------------------------------


    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {

        List<LTL<L>> pnf = new LinkedList<>();
        LTL2PNF(ltl, pnf);

        Set<Set<LTL<L>>> closure = new HashSet<>();
        createClosure(pnf, closure);

        MultiColorAutomaton<Set<LTL<L>>, L> gnba = createGNBA(closure, pnf);

        // inits
        for(Set<LTL<L>> state : gnba.getTransitions().keySet()){
            if(state.contains(ltl))
                gnba.setInitial(state);
        }

        setAcceptingStates(gnba, pnf);

        return GNBA2NBA(gnba);
    }

    private <L> void LTL2PNF(LTL<L> ltl, List<LTL<L>> pnf){

        if(ltl instanceof TRUE || ltl instanceof AP){
            if(!pnf.contains(ltl))
                pnf.add(ltl);
        }
        else if(ltl instanceof Not){
            LTL2PNF(((Not<L>) ltl).getInner(), pnf);
        }
        else if(ltl instanceof Next){
            LTL2PNF(((Next<L>) ltl).getInner(), pnf);
            if(!pnf.contains(ltl))
                pnf.add(ltl);
        }
        else if(ltl instanceof And){
            LTL2PNF(((And<L>) ltl).getLeft(), pnf);
            LTL2PNF(((And<L>) ltl).getRight(), pnf);
            if(!pnf.contains(ltl))
                pnf.add(ltl);
        }
        else if(ltl instanceof Until){
            LTL2PNF(((Until<L>) ltl).getLeft(), pnf);
            LTL2PNF(((Until<L>) ltl).getRight(), pnf);
            if(!pnf.contains(ltl))
                pnf.add(ltl);
        }
    }

    private <L> void createClosure(List<LTL<L>> pnf, Set<Set<LTL<L>>> states) {
        //true
        if(pnf.contains(LTL.true_())){
            Set<LTL<L>> state = new HashSet<>();
            state.add(LTL.true_());
            states.add(state);
        }
        else{
            states.add(new HashSet<>());
        }

        for(LTL<L> ltl : pnf){
            //AP | Next
            if(ltl instanceof AP || ltl instanceof Next){
                Set<Set<LTL<L>>> iter = new HashSet<>(states);
                for(Set<LTL<L>> state : iter){
                    addStates(states, state, ltl);
                }
            }
            //Until
            else if(ltl instanceof Until){
                Set<Set<LTL<L>>> iter = new HashSet<>(states);
                for(Set<LTL<L>> state : iter){
                    if(state.contains(((Until<L>) ltl).getRight()))
                        state.add(ltl);
                    else if(state.contains(((Until<L>) ltl).getLeft())){
                        addStates(states, state, ltl);
                    }
                    else
                        state.add(LTL.not(ltl));
                }
            }
            //And
            else if(ltl instanceof And){
                Set<Set<LTL<L>>> iter = new HashSet<>(states);
                for(Set<LTL<L>> state : iter){
                    if(state.contains(((And<L>) ltl).getLeft()) && state.contains(((And<L>) ltl).getRight()))
                        state.add(ltl);
                    else
                        state.add(LTL.not(ltl));
                }
            }


        }
    }

    private <L> void addStates(Set<Set<LTL<L>>> states, Set<LTL<L>> state, LTL<L> ltl){
        Set<LTL<L>> neg = new HashSet<>(state);
        state.add(ltl);
        neg.add(LTL.not(ltl));
        states.add(neg);
    }

    private <L> void setAcceptingStates(MultiColorAutomaton<Set<LTL<L>>, L> gnba, List<LTL<L>> pnf){

        List<LTL<L>> untils = new ArrayList<>();
        for(LTL<L> ltl : pnf){
            if(ltl instanceof Until)
                untils.add(ltl);
        }

        if(untils.size() > 0) {
            for(Set<LTL<L>> state : gnba.getTransitions().keySet()){
                for(LTL<L> until : untils){
                    if(!state.contains(until) || state.contains(((Until<L>)until).getRight()))
                        gnba.setAccepting(state, untils.indexOf(until));
                }
            }
        }
        else{
            for (Set<LTL<L>> state : gnba.getTransitions().keySet()) {
                gnba.setAccepting(state, 0);
            }
        }
    }

    private <L> MultiColorAutomaton<Set<LTL<L>>, L> createGNBA(Set<Set<LTL<L>>> closure, List<LTL<L>> pnf){
        Set<Until<L>> until = new HashSet<>();
        Set<Next<L>> next = new HashSet<>();
        for(LTL<L> ltl : pnf){
            if(ltl instanceof Until)
                until.add((Until<L>)ltl);
            else if(ltl instanceof Next)
                next.add((Next<L>)ltl);

        }

        MultiColorAutomaton<Set<LTL<L>>, L> aut = new MultiColorAutomaton<>();
        for(Set<LTL<L>> source : closure){
            for(Set<LTL<L>> dest : closure){
                //next
                boolean createTranNext = handleNext(next, source, dest);
                //until
                boolean createTranUntil = handleUntil(until, source, dest);
                //AP
                handleAP(aut, source, dest, createTranNext&&createTranUntil);
            }
        }
        return aut;
    }

    private <L> void handleAP(MultiColorAutomaton<Set<LTL<L>>, L> aut, Set<LTL<L>> source, Set<LTL<L>> dest, boolean createTran) {
        if(createTran){
            Set<L> ap = new HashSet<>();
            for(LTL<L> ltl : source){
                if(ltl instanceof AP)
                    ap.add(((AP<L>) ltl).getName());
                aut.addTransition(source, ap, dest);
            }
        }
    }

    private <L> boolean handleUntil(Set<Until<L>> until, Set<LTL<L>> source, Set<LTL<L>> dest) {
        for(Until<L> l1 : until){
            if(source.contains(l1.getRight()) || (source.contains(l1.getLeft()) && dest.contains(l1))){
                if(!source.contains(l1)){
                    return false;
                }
            }
            else if(source.contains(l1)){
                return false;
            }
        }
        return true;
    }

    private <L> boolean handleNext(Set<Next<L>> next, Set<LTL<L>> source, Set<LTL<L>> dest) {
        for(Next<L> l1 : next){
            if(source.contains(l1)){
                if(!dest.contains(l1.getInner())){
                    return false;
                }
            }
            else if(dest.contains(l1.getInner())){
                return false;
            }
        }
        return true;
    }


    //------------------------------------------------------------------------------------------------------

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        return GNBA2NBA_WithCopies(mulAut);
    }

    private <S, L> Automaton<Pair<S, Integer>, L> GNBA2NBA_WithCopies(MultiColorAutomaton<S, L> mulAut){
        Automaton<Pair<S, Integer>, L> aut = new Automaton<>();

        List<Integer> copies = new ArrayList<>(mulAut.getColors());

        for(Integer copy : copies){
            int nextCopy = getNext(copy, copies);

            for(Map.Entry<S, Map<Set<L>, Set<S>>> tran : mulAut.getTransitions().entrySet()){
                Pair<S, Integer> from = new Pair<>(tran.getKey(), copy);
                AddTransitions(tran, copy, nextCopy, mulAut, from, aut);

                if(copies.indexOf(copy) == 0){//Add initial and accepting states
                    AddInitsAndAccepting(mulAut, tran, copy, aut, from);
                }
            }
        }
        return aut;
    }

    private int getNext(Integer copy, List<Integer> copies){
        if(!copy.equals(copies.get(copies.size()-1)))
            return copies.get(copies.indexOf(copy)+1);
        else
            return copies.get(0);
    }

    private <S,L> void AddInitsAndAccepting(MultiColorAutomaton<S, L> mulAut, Map.Entry<S,
            Map<Set<L>, Set<S>>> tran,Integer copy, Automaton<Pair<S, Integer>, L> aut,  Pair<S, Integer> from){
        if(mulAut.getInitialStates().contains(tran.getKey()))
            aut.setInitial(from);
        if(mulAut.getAcceptingStates(copy).contains(tran.getKey()))
            aut.setAccepting(from);
    }

    private <S,L> void AddTransitions(Map.Entry<S, Map<Set<L>, Set<S>>> tran, Integer copy, Integer nextCopy,
             MultiColorAutomaton<S, L> mulAut, Pair<S, Integer> from, Automaton<Pair<S, Integer>, L> aut) {
        for (Map.Entry<Set<L>, Set<S>> action : tran.getValue().entrySet()) {
            for (S state : action.getValue()) {//add transitions
                if (!mulAut.getAcceptingStates(copy).contains(tran.getKey()))
                    aut.addTransition(from, action.getKey(), new Pair<>(state, copy));
                else
                    aut.addTransition(from, action.getKey(), new Pair<>(state, nextCopy));
            }
        }
    }

}




