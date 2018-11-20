package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
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
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }
   
}
