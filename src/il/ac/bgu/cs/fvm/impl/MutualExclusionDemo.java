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
            System.out.println("MUTUAL EXCLUSION test:");
            System.out.println("Build an automata for the complementary language - a language that accepts a state" +
                    "\nwith the labels \"crit1 and crit2\".");
            Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhiAut(a -> a.contains("crit1") && a.contains("crit2"));
            System.out.println("Verify whether the ts satisfies the omega regular property:");
            System.out.println("Build the predict. ");
            System.out.println("For each reachable state s in the product of ts and automata: ");
            System.out.println("    Check if the s satisfied the predicate");
            System.out.println("    If not - check if is part of a cycle in ts");
            System.out.println("        If cycle found - ts doesn't satisfy the omega regular property- " +
                             "\n        2 processes are in the critical section at the same time = no mutual exclusion." );
            System.out.println("    If not exist such s - ts satisfies the omega regular property -" +
                             "\n    ts is providing mutual exclusion" );
            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
            System.out.println("The result is " + (vr instanceof VerificationSucceeded ? "succeeded" : "failed"));
        }

        System.out.println();
        // Test a liveness property - that after every state that satisfies
        // wait1 we must eventually have a state that satisfies crit1
        {
            System.out.println("LIVENESS test:");
            System.out.println("Build an automata for the complementary language - a language in which a state" +
                    "\nwith the label \"wait\" is reached and a state with the label \"crit\" is not reach afterwords.");
            Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhi1AndThenAlwaysPhi2Aut(a -> a.contains("wait1"), a -> !a.contains("crit1"));
            System.out.println("Verify whether the ts satisfies the omega regular property:");
            System.out.println("Build the predict. ");
            System.out.println("For each reachable state s in the product of ts and automata: ");
            System.out.println("    check if the s satisfied the predicate");
            System.out.println("    If not - check if is part of a cycle in ts");
            System.out.println("        If cycle found - ts doesn't satisfy the omega regular property- " +
                             "\n        process has been waiting and didn't get into the critical section = no liveness." );
            System.out.println("    If not exist such s - ts satisfies the omega regular property -" +
                             "\n    ts is providing liveness" );
            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
            System.out.println("The result is " + (vr instanceof VerificationSucceeded ? "succeeded" : "failed"));
        }


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
