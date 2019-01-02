package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.examples.PetersonProgramGraphBuilder;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

public class MutualExclusionDemo {

    public static void main(String[] args){
        peterson();
    }

    public static void peterson() {
        FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

        System.out.println("build 2 program graphs");
        ProgramGraph<String, String> pg1 = PetersonProgramGraphBuilder.build(1);
        ProgramGraph<String, String> pg2 = PetersonProgramGraphBuilder.build(2);

        System.out.println("interleave the two program graphs");
        ProgramGraph<Pair<String, String>, String> pg = fvmFacadeImpl.interleave(pg1, pg2);

        System.out.println("create acts and defenitions for the new transition system");
        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());

        System.out.println("create transition system from the interleaved program graph");
        TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts;
        ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);

        System.out.println("add labels to ts");
        addLabels(ts);

        // Test mutual exclusion
        {
            System.out.println("mutual exclusion");
            System.out.println("predicat = {crit1, crit2}");
            Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhiAut(a -> a.contains("crit1") && a.contains("crit2"));
            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);

        }

        // Test a liveness property - that after every state that satisfies
        // wait1 we must eventually have a state that satisfies crit1
        {
            Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhi1AndThenAlwaysPhi2Aut(a -> a.contains("wait1"), a -> !a.contains("crit1"));
            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);

        }

        System.out.println("works!");
    }

    // Add labels to ts for formulating mutual exclusion properties.
    private static void addLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        FvmFacade fvmFacadeImpl = FvmFacade.createInstance();
        ts.getStates().stream().forEach(st -> ts.getAtomicPropositions().stream().forEach(ap -> ts.removeLabel(st, ap)));

        Set<String> aps = new HashSet<>(ts.getAtomicPropositions());
        aps.stream().forEach(ap -> ts.removeAtomicProposition(ap));

        seq("wait1", "wait2", "crit1", "crit2", "crit1_enabled").stream().forEach(s -> ts.addAtomicPropositions(s));

        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1"));
        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "wait1"));

        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2"));
        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "wait2"));

        Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
        ts.getStates().stream().filter(s -> fvmFacadeImpl.post(ts, s).stream().anyMatch(_crit1)).forEach(s -> ts.addToLabel(s, "crit1_enabled"));
    }
}
