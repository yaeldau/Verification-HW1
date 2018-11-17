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
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
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
