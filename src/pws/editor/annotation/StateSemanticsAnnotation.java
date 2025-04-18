package pws.editor.annotation;

import pws.PWSState;
import pws.editor.PWSStateMachinePanel;
import pws.PWSStateMachine;
import java.util.*;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.List;

public class StateSemanticsAnnotation extends Annotation<PWSState> {

    public StateSemanticsAnnotation(PWSState content) {
        super(content);
        setOpaque(true);
        setBackground(Color.WHITE);
        setBorder(BorderFactory.createLineBorder(Color.red, 1));
    }

    @Override
    protected void showPopup(MouseEvent e) {
        // Create a popup with a single disabled menu item.
        JPopupMenu popup = new JPopupMenu();
        JMenuItem notModifiable = new JMenuItem("Annotazione non modificabile");
        notModifiable.setEnabled(false);
        popup.add(notModifiable);
        popup.show(this, e.getX(), e.getY());
    }

    @Override
    protected String buildDisplayText() {
        return "";
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        Graphics2D g2d = (Graphics2D) g;
        g2d.setFont(getFont().deriveFont(Font.PLAIN, 12f));
        g2d.setColor(Color.BLACK);

        if (content == null) return;

        PWSState state = content;
        FontMetrics fm = g2d.getFontMetrics();

        int padding = 4;
        int y = fm.getHeight() + padding;
        // 1) Constraint semantics (blue, centered)
        String constraintSem = (state.getConstraintsSemantics() == null ? "" : state.getConstraintsSemantics().toString());
        g2d.setColor(Color.BLUE);
        int w1 = fm.stringWidth(constraintSem);
        g2d.drawString(constraintSem, (getWidth() - w1) / 2, y);

        // 2) Actual state semantics: each configuration green if in constraints, red otherwise
        y += fm.getHeight();
        Set<?> constraintsConfigs = state.getConstraintsSemantics() == null
                ? Collections.emptySet()
                : state.getConstraintsSemantics().getConfigurations();
        Set<?> stateConfigs = state.getStateSemantics() == null
                ? Collections.emptySet()
                : state.getStateSemantics().getConfigurations();
        // prepare string set of constraint configurations
        Set<String> constraintStrs = new HashSet<>();
        for (Object cfg : constraintsConfigs) {
            constraintStrs.add(cfg.toString());
        }
        List<String> cfgStrs = new ArrayList<>();
        for (Object cfg : stateConfigs) {
            cfgStrs.add(cfg.toString());
        }
        int totalWidth = 0;
        for (String s : cfgStrs) {
            totalWidth += fm.stringWidth(s) + fm.charWidth(' ');
        }
        int x = (getWidth() - totalWidth) / 2;
        for (String s : cfgStrs) {
            boolean contained = constraintStrs.contains(s);
            g2d.setColor(contained ? Color.GREEN.darker() : Color.RED);
            g2d.drawString(s, x, y);
            x += fm.stringWidth(s) + fm.charWidth(' ');
        }

        // 3) Reactive exit zones: green if covered, red otherwise
        y += fm.getHeight();
        int ezX = padding;
        try {
            PWSStateMachine sm = ((PWSStateMachinePanel) getParent()).getStateMachine();
            Set<smalgebra.BasicStateProposition> covered = new HashSet<>();
            for (machinery.TransitionInterface ti : sm.getTransitions()) {
                if (ti instanceof pws.PWSTransition) {
                    pws.PWSTransition pt = (pws.PWSTransition) ti;
                    if (!pt.isTriggerable() && pt.getSource() == state
                            && pt.getGuardProposition() instanceof smalgebra.BasicStateProposition) {
                        covered.add((smalgebra.BasicStateProposition) pt.getGuardProposition());
                    }
                }
            }
            for (pws.editor.semantics.ExitZone ez : state.getReactiveSemantics()) {
                String txt = ez.toString();
                boolean isCovered = covered.contains(ez.getTarget());
                g2d.setColor(isCovered ? Color.GREEN.darker() : Color.RED);
                g2d.drawString(txt, ezX, y);
                ezX += fm.stringWidth(txt) + fm.charWidth(' ');
            }
        } catch (Exception ignored) {
        }
    }

    @Override
    public Dimension getPreferredSize() {
        if (content == null) return new Dimension(100, 50);

        PWSState state = content;
        String constraintSem = (state.getConstraintsSemantics() == null) ? "" : state.getConstraintsSemantics().toString();
        String actualSem = (state.getStateSemantics() == null) ? "" : state.getStateSemantics().toString();
        String autonomousSem = (state.getReactiveSemantics() == null) ? "" : state.getReactiveSemantics().toString();

        String[] lines = new String[] { constraintSem, actualSem, autonomousSem };
        FontMetrics fm = getFontMetrics(getFont().deriveFont(Font.PLAIN, 12f));
        int maxWidth = 0;
        for (String line : lines) {
            maxWidth = Math.max(maxWidth, fm.stringWidth(line));
        }
        int totalHeight = fm.getHeight() * lines.length;
        // Add padding
        return new Dimension(maxWidth + 10, totalHeight + 10);
    }
}