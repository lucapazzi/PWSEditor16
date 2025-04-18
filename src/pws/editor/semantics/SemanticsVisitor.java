package pws.editor.semantics;

import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

import machinery.StateInterface;
import pws.PWSState;
import pws.PWSStateMachine;
import pws.PWSTransition;
import machinery.TransitionInterface;
import assembly.Assembly;

/**
 * Visitor that computes fixed‑point semantics for all states in a PWSStateMachine.
 * Each state’s semantics is the union of the contributions of its incoming
 * transitions, where:
 *
 * <ul>
 *   <li>triggerable (and initial) transitions apply their guard AND then any actions to
 *       the source state’s <i>stateSemantics</i>;</li>
 *   <li>reactive (autonomous) transitions apply internal transformations
 *       (via ExitZone) to the source state’s <i>reactiveSemantics</i> and then any actions.</li>
 * </ul>
 */
public class SemanticsVisitor {
    private static final Logger logger = Logger.getLogger(SemanticsVisitor.class.getName());

    /**
     * Iteratively computes a semantics map for every PWSState until convergence.
     */
    public static Map<PWSState, Semantics> computeAllStateSemantics(PWSStateMachine machine) {
        logger.info("Starting fixed-point semantics computation for machine '" + machine.getName() + "'.");

        Assembly asm = machine.getAssembly();
        Map<PWSState, Semantics> semMap = new HashMap<>();
        for (StateInterface s : machine.getStates()) {
            semMap.put((PWSState) s, Semantics.bottom(asm.getAssemblyId()));
        }
        boolean changed = true;
        int iter = 0;
        int maxIter = 1000; // example cap, adjust as necessary
        while (changed && iter < maxIter) {
            changed = false;
            for (StateInterface s : machine.getStates()) {
                Semantics newSem = computeStateSemanticsOnce((PWSState) s, machine, semMap);
                if (!newSem.equals(semMap.get(s))) {
                    semMap.put((PWSState) s, newSem);
                    changed = true;
                }
            }
            iter++;
        }
        if (iter >= maxIter) {
            logger.warning("SemanticsVisitor reached iteration cap (" + maxIter + " iterations) for machine '" + machine.getName() + "'. Results may not have fully converged.");
        }
        logger.info("Completed semantics computation in " + iter + " iterations for machine '" + machine.getName() + "'.");

        return semMap;
    }

    private static Semantics computeStateSemanticsOnce(
            PWSState target,
            PWSStateMachine machine,
            Map<PWSState, Semantics> currentMap) {

        Assembly asm = machine.getAssembly();
        Semantics agg = Semantics.bottom(asm.getAssemblyId());

        for (TransitionInterface ti : machine.getTransitions()) {
            if (!(ti instanceof PWSTransition)) continue;
            PWSTransition t = (PWSTransition) ti;
            if (t.getTarget() != target) continue;
            PWSState src = (PWSState) t.getSource();
            Semantics contrib;

            if (t.isTriggerable() || src.isPseudoState()) {
                // triggerable or initial
                Semantics base = currentMap.get(src);
                Semantics guardSem = t.getGuardProposition().toSemantics(asm);
                contrib = base.AND(guardSem);
            } else {
                // reactive/autonomous
                Semantics base = convertReactive(src.getReactiveSemantics(), asm);
                contrib = Semantics.bottom(asm.getAssemblyId());
                for (ExitZone ez : src.getReactiveSemantics()) {
                    if (ez.getTarget().equals(t.getGuardProposition())) {
                        Semantics frag = base.transformByMachineTransition(
                                ez.getStateMachineId(),
                                ez.getTransition(), asm);
                        contrib = contrib.OR(frag);
                    }
                }
            }
            // apply actions
            for (var a : t.getActionList()) {
                contrib = contrib.transformByMachineEvent(a.getMachineId(), a.getEvent(), asm);
            }
            // aggregate
            agg = agg.OR(contrib);
        }

        return agg;
    }

    private static Semantics convertReactive(
            Collection<ExitZone> zones,
            Assembly asm) {
        Semantics result = Semantics.bottom(asm.getAssemblyId());
        for (ExitZone ez : zones) {
            result = result.OR(ez.getSource()
                    .toSemantics(asm));
        }
        return result;
    }
}