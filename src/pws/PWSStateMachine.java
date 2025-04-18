package pws;

import assembly.Action;
import assembly.Assembly;
import machinery.*;
import pws.editor.semantics.ExitZone;
import pws.editor.semantics.Semantics;
import pws.editor.semantics.SemanticsVisitor;
import smalgebra.BasicStateProposition;

import java.awt.*;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

public class PWSStateMachine extends StateMachine {
    // Field to hold the Assembly that belongs to this PWSStateMachine.
    private Assembly assembly;

    private static final long serialVersionUID = 1L;

    // Default constructor.
//    public PWSStateMachine() {
//        super();
//        // Automatically instantiate a default assembly.
//        this.setAssembly(new Assembly("PWSEditorAssembly"));
//        fixPseudoState();
//    }

    // Constructor that accepts a name.
    public PWSStateMachine(String name) {
        super(name);
        // Instantiate a default assembly.
        this.setAssembly(new Assembly("PWSEditorAssembly"));
        fixPseudoState();
    }

//    // Constructor that accepts a name and an Assembly.
//    public PWSStateMachine(String name, Assembly assembly) {
//        super();
//        this.setName(name);
//        // Use the provided assembly.
//        this.setAssembly(assembly);
//        fixPseudoState();
//    }

    // Constructor that accepts an Assembly.
//    public PWSStateMachine(Assembly assembly) {
//        super();
//        // Instantiate with the provided assembly.
//        this.setAssembly(assembly);
//        fixPseudoState();
//    }

    // Getter for the assembly.
    public Assembly getAssembly() {
        return assembly;
    }

    // Setter for the assembly.
    public void setAssembly(Assembly assembly) {
        this.assembly = assembly;
    }

    /**
     * Metodo privato per sostituire il pseudostato creato nel costruttore base con un PWSState.
     * Viene rimosso l'oggetto creato di default e sostituito con un'istanza di PWSState.
     */
    private void fixPseudoState() {
        if (!states.isEmpty() && states.get(0).getName().equals("PseudoState")) {
            states.remove(0);
        }
        // Crea il nuovo pseudostato come PWSState
        PWSState pseudo = new PWSState("PseudoState", new Point(20, 20), this.assembly);
        this.pseudoState = pseudo;
        states.add(0, pseudo);
    }

    /**
     * Recalculates and applies the semantics for all states and transitions in this PWSStateMachine.
     *
     * Steps performed:
     * 1) Initialize the pseudostate semantics by calling assembly.calculateInitialStateSemantics().
     * 2) Compute a fixed-point over all other states' semantics via SemanticsVisitor.
     * 3) Assign the newly computed semantics back to each PWSState, skipping the pseudostate to preserve its initial semantics.
     * 4) Update each PWSTransition’s transitionSemantics by computing its pre- and post-conditions.
     */
    public void recalculateSemantics() {
        // 1) Initialize the pseudostate semantics by calling assembly.calculateInitialStateSemantics().
        if (pseudoState instanceof PWSState) {
            PWSState pseudo = (PWSState) pseudoState;
            Semantics init = assembly.calculateInitialStateSemantics();
            pseudo.setStateSemantics(init);
        }

        // 2) Compute semantics for each non-pseudostate by folding incoming transitions
        for (StateInterface s : this.getStates()) {
            if (s instanceof PWSState && s != this.pseudoState) {
                PWSState ps = (PWSState) s;
                Semantics sem = computeStateSemantics(ps);
                ps.setStateSemantics(sem);
            }
        }
        // 3) Update each PWSTransition’s transitionSemantics by computing its pre- and post-conditions.
        for (TransitionInterface t : transitions) {
            if (t instanceof PWSTransition) {
                PWSTransition pt = (PWSTransition) t;
                Semantics ts = computeTransitionSemantics(pt);
                pt.setTransitionSemantics(ts);
            }
        }
    }

    public Semantics computeTransitionSemantics(PWSTransition t) {
        // Recupera lo stato sorgente della transizione
        PWSState pwsState = (PWSState) t.getSource();

        // determino la precondizione della trasformazione attuata dalla semantica
        Semantics pre;
        // Se la transizione è triggerabile OPPURE se lo stato sorgente è un pseudostato,
        // usa lo stateSemantics; altrimenti (transizione autonoma/reattiva) usa reactiveSemantics.
        Semantics stateSemantics = pwsState.getStateSemantics();
        if (t.isTriggerable() || pwsState.isPseudoState()) {
            // Recupera la semantica della guardia della transizione
            Semantics guard = t.getGuardProposition().toSemantics(assembly);
            // Calcola l'intersezione (AND) fra la semantica dello stato sorgente e la guardia.
            pre = stateSemantics.AND(guard);
        } else { // Reactive transitions
            // uso la proposizione base di stato a guardia della transizione (bspGuardTrans);
            BasicStateProposition bspGuardTrans = (BasicStateProposition) t.getGuardProposition();
            pre = Semantics.bottom(assembly);
            // itero sulle EZ associate allo stato
            for (ExitZone ez : pwsState.getReactiveSemantics()) {
                // se il target di una EZ coincide con la guardia della transizione
                if (ez.getTarget().equals(bspGuardTrans)) {
                    // devo trasformare la semantica dello stato in conseguenza della transizione
                    Semantics internalTransformation = stateSemantics.transformByMachineTransition(
                            ez.getStateMachineId(),
                            ez.getTransition(),
                            assembly
                    );
                    // sommo (OR) le varie trasformazioni interne relative al trigger
                    pre = pre.OR(internalTransformation);
                    // break;
                }
            }
        }

        // Applica la trasformazione derivante dalle azioni associate alla transizione.
        for (Action a : t.getActionList()) {
            pre = pre.transformByMachineEvent(
                    a.getMachineId(),
                    a.getEvent(),
                    assembly
            );
        }

        return pre;
    }

    public Semantics computeStateSemantics(PWSState s) {
        Semantics orSem = Semantics.bottom(assembly.getAssemblyId());

        // Calcola la semantica dalle transizioni entranti
        List<TransitionInterface> incoming = s.getIncomingTransitions();
        if (incoming != null) {
            for (TransitionInterface t : incoming) {
                if (t instanceof PWSTransition) {
                    Semantics ts = computeTransitionSemantics((PWSTransition) t);
                    orSem = (orSem.getConfigurations().isEmpty()) ? ts : orSem.OR(ts);
                }
            }
        }

        // Calcola la semantica autonoma separatamente
        HashSet<ExitZone> reactiveSem = computeReactiveSemantics(orSem);

        // Potrebbe essere utile assegnare le nuove semantiche al PWSState, per esempio:
        s.setReactiveSemantics(reactiveSem);
        // Per quanto riguarda le constraints, potremmo aggiungere una logica simile in futuro.

//
        return orSem;
    }

    public HashSet<ExitZone> computeReactiveSemantics(Semantics baseSemantics) {
        HashSet<ExitZone> reactiveSem = new HashSet<>();
        Map<String, StateMachine> stateMachines = assembly.getStateMachines();
        if (stateMachines != null) {
            for (Map.Entry<String, StateMachine> entry : stateMachines.entrySet()) {
                String machineId = entry.getKey();
                StateMachine machine = entry.getValue();
                List<TransitionInterface> allTransitions = machine.getTransitions();
                if (allTransitions != null) {
                    for (TransitionInterface t : allTransitions) {
                        if (t instanceof Transition) {
                            Transition transition = (Transition) t;
                            if (transition.isAutonomous()) {
                                State sourceState = (State) transition.getSource();
                                State targetState = (State) transition.getTarget();
                                BasicStateProposition bs_source = new BasicStateProposition(machineId, sourceState.getName());
                                BasicStateProposition bs_target = null;
                                // una trans. autononome da luogo a una EZ se e solo se:
                                // - la sorgente della bsp ha un'intersezione non nulla con la sem. dello stato
                                // - il target della bsp ha un'intersezione nulla con la sem. dello stato
                                Semantics sourceAndSem = bs_source.toSemantics( assembly ).AND(baseSemantics);
                                if( !sourceAndSem.ISEMPTY()) {
                                    bs_target = new BasicStateProposition(machineId, targetState.getName());
                                    Semantics targetAndSem = bs_target.toSemantics( assembly ).AND(baseSemantics);
                                    if( targetAndSem.ISEMPTY()) {
                                        ExitZone ez = new ExitZone(
                                                machineId,
                                                transition,
                                                bs_source,
                                                bs_target
                                        );
                                        reactiveSem.add(ez);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return reactiveSem;
    }

    @Override
    public PWSStateMachine clone() {
        PWSStateMachine cloned = new PWSStateMachine(this.getName());
        cloned.setAssembly(this.getAssembly());
        // Nota: Per clonare gli stati e le transizioni, occorre implementare la logica di copia,
        // che può essere definita in base alle esigenze.
        return cloned;
    }
}