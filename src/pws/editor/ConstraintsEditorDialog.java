package pws.editor;

import pws.PWSState;
import pws.editor.semantics.Semantics;
import pws.editor.ConstraintsEditorDialog; // Import added
import assembly.Assembly; // Import added
import smalgebra.BasicStateProposition;

import javax.swing.*;
import java.awt.*;

public class ConstraintsEditorDialog extends JDialog {
    private JTextArea textArea;
    private JButton applyButton, cancelButton;
    private PWSState state;  // the state whose constraint semantics we're editing
    private Assembly assembly; // Added field

    public ConstraintsEditorDialog(PWSState state, Assembly assembly) { // Modified constructor
        this.state = state;
        this.assembly = assembly;
        setModal(true);
        setTitle("Edit Constraints Semantics");
        textArea = new JTextArea(10, 30);
        // Prepopulate with current constraints semantics
        textArea.setText(getConstraintsTextFromState(state));

        applyButton = new JButton("Apply");
        cancelButton = new JButton("Cancel");

        applyButton.addActionListener(e -> {
            String text = textArea.getText();
            Semantics newConstraints = parseConfigurations(text);
            state.setConstraintsSemantics(newConstraints);
            dispose();
        });
        cancelButton.addActionListener(e -> dispose());

        JPanel buttonPanel = new JPanel();
        buttonPanel.add(applyButton);
        buttonPanel.add(cancelButton);
        add(new JScrollPane(textArea), BorderLayout.CENTER);
        add(buttonPanel, BorderLayout.SOUTH);
        pack();
        setLocationRelativeTo(null);
    }

    private Semantics parseConfigurations(String text) {
        // For each non-empty line in text, parse the configuration, then union them
        Semantics result = Semantics.bottom(assembly); // Modified call
        for (String line : text.split("\\n")) {
            if (!line.trim().isEmpty()) {
                // Here, parse each line into a Semantics object.
                Semantics confSem = parseConfigurationLine(line.trim());
                result = result.OR(confSem);
            }
        }
        return result;
    }

    private Semantics parseConfigurationLine(String line) {
        // A simple parser for a configuration line of the format:
        // "M1: stateA, M2: stateB, ..."
        String[] pairs = line.split(",");
        // Start with the top semantics (i.e., universal configuration)
        Semantics configSem = Semantics.top(assembly); // Modified call
        for (String pair : pairs) {
            String[] parts = pair.split(":");
            if (parts.length == 2) {
                String machine = parts[0].trim();
                String machineState = parts[1].trim();
                // Create a basic state proposition from the machine and machineState
                BasicStateProposition bsp = new BasicStateProposition(machine, machineState);
                // Convert the proposition into a configuration semantics
                Semantics propositionSem = bsp.toSemantics(assembly); // Modified call
                // Combine the constraint using AND, as all conditions must hold
                configSem = configSem.AND(propositionSem);
            }
        }
        return configSem;
    }

    private String getConstraintsTextFromState(PWSState state) {
        // Convert the current constraints semantics into a text representation
        // that can be edited.
        return state.getConstraintsSemantics().toString();
    }
}