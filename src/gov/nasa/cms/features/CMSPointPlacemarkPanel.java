/*
 * Copyright (C) 2012 United States Government as represented by the Administrator of the
 * National Aeronautics and Space Administration.
 * All Rights Reserved.
 */
package gov.nasa.cms.features;

import gov.nasa.worldwind.View;
import gov.nasa.worldwind.*;
import gov.nasa.worldwind.geom.Position;
import gov.nasa.worldwind.layers.RenderableLayer;
import gov.nasa.worldwind.render.*;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.text.*;
import java.awt.*;
import java.awt.event.*;
import java.math.RoundingMode;
import java.text.*;

import static javax.swing.JOptionPane.*;

/**
 * Measure Tool control panel for <code>{@link gov.nasa.cms.features.MeasureDialog}</code>.
 * Allows users to pick from 8 different shape drawing options. Also has the ability
 * to export Measure Tool statistics to a CSV file.
 *
 * @see gov.nasa.worldwind.util.measure.MeasureTool
 * @author kjdickin
 */
public class CMSPointPlacemarkPanel extends JPanel
{

    private WorldWindow wwd;

    private JComboBox colorCombo;
    private JTextField latTextField;
    private JTextField lonTextField;
    private JTextField elevTextField;
    private JTextField labelTextField;
    private JTextField scaleTextField;
    private JButton labelColorButton;
    private JCheckBox showLabelCheck;
    private JButton addButton;
    private JButton viewButton;

    private JButton endButton;
    private JCheckBox followCheck;
    private JButton deleteButton;
    private JLabel[] pointLabels;
    private JLabel lengthLabel;
    private JLabel areaLabel;
    private JLabel widthLabel;
    private JLabel heightLabel;
    private JLabel headingLabel;
    private JLabel centerLabel;
    private JPanel coordinatesPanel;
    private JLabel resultLabel;
    private JPanel resultPanel;
    private JButton flyToCoordinates;

    
    private PointPlacemark placemark;
    private RenderableLayer layer;
    private PointPlacemarkAttributes attrs;
    
    private double latLocation;
    private double lonLocation;
    private double elevLocation;

    public CMSPointPlacemarkPanel(WorldWindow wwdObject)
    {
        super(new BorderLayout());
        this.wwd = wwdObject;
        
        JPanel mainPanel = new JPanel();
        mainPanel.setOpaque(false);
        this.makePanel(mainPanel);     
    }

    private void makePanel(JPanel panel)
    {
        placemark = new PointPlacemark(Position.fromDegrees(0, 0, 1e4));
        layer = new RenderableLayer();
        attrs = new PointPlacemarkAttributes();
        
        //======== Measurement Panel ========  
        JPanel colorPanel = new JPanel(new GridLayout(1, 2, 5, 5));
        colorPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        colorPanel.add(new JLabel("Color:"));
        colorCombo = new JComboBox<>(new String[]
        {
            "Red","Orange", "Yellow", "Green", "Blue", "Purple", "White", "Black", "Gray"
        });
        colorCombo.setSelectedIndex(0);

        // Setting default pin to Red, otherwise a yellow smaller pin is shown by default.
        attrs.setImageAddress("images/pushpins/plain-red.png");

        colorCombo.addActionListener((ActionEvent event) ->
        {
            String item = (String) ((JComboBox) event.getSource()).getSelectedItem();
            if (item != null)
            {
                switch (item)
                {
                    case "Red":
                        attrs.setImageAddress("images/pushpins/plain-red.png");
                        break;
                    case "Orange":
                        attrs.setImageAddress("images/pushpins/plain-orange.png");
                        break;
                    case "Yellow":
                        attrs.setImageAddress("images/pushpins/plain-yellow.png");
                        break;
                    case "Green":
                        attrs.setImageAddress("images/pushpins/plain-green.png");
                        break;
                    case "Blue":
                        attrs.setImageAddress("images/pushpins/plain-blue.png");
                        break;
                    case "Purple":
                        attrs.setImageAddress("images/pushpins/plain-purple.png");
                        break;
                    case "White":
                        attrs.setImageAddress("images/pushpins/plain-white.png");
                        break;
                    case "Black":
                        attrs.setImageAddress("images/pushpins/plain-black.png");
                        break;
                    case "Gray":
                        attrs.setImageAddress("images/pushpins/plain-gray.png");
                        break;
                    default:
                        break;
                }
            } else {
                attrs.setImageAddress("images/pushpins/plain-red.png");
            }
        });
        colorPanel.add(colorCombo);

        //======== Coordinates Panel ========
//        JPanel coordinatesLabelPanel = new JPanel(new GridLayout(1, 1, 5, 5));
//        coordinatesLabelPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
//        coordinatesLabelPanel.add(new JLabel("Coordinates (lat, lon):"));
//
//        this.coordinatesPanel = new JPanel(new GridBagLayout());
//        coordinatesPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
//        GridBagConstraints gbc;
//
//        this.coordinatesTextField = new JTextField();
//        gbc = new GridBagConstraints();
//        gbc.fill = GridBagConstraints.HORIZONTAL;
//        gbc.gridwidth = 2;
//        gbc.gridx = 0;
//        gbc.gridy = 0;
//        gbc.insets = new Insets(0, 0, 0, 5);
//        gbc.weightx = .7;
//        gbc.ipadx = 15;
//        gbc.anchor = GridBagConstraints.LINE_START;
//        coordinatesPanel.add(coordinatesTextField, gbc);
//
//        this.flyToCoordinates = new JButton("Validate");
////        flyToCoordinates.setPreferredSize(new Dimension(30,15));
//        gbc = new GridBagConstraints();
//        gbc.fill = GridBagConstraints.HORIZONTAL;
//        gbc.gridwidth = 1;
//        gbc.gridx = 4;
//        gbc.gridy = 0;
//        gbc.insets = new Insets(0, 0, 0, 0);
//        gbc.weightx = .05;
////        gbc.ipadx = 10;
//        gbc.anchor = GridBagConstraints.LINE_END;
//        coordinatesPanel.add(flyToCoordinates, gbc);


//        this.coordinatesTextField.addActionListener(flyToCoordinatesListener);
//        this.flyToCoordinates.addActionListener(flyToCoordinatesListener);
//
//        this.resultPanel = new JPanel(new GridLayout(0,1,5,5));
//        resultPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
//        this.resultLabel = new JLabel("-90°<=Lat<=90°, -180°<=Long<=180°");
////        this.resultLabel = new JLabel("1");
//        this.resultLabel.setHorizontalTextPosition(JLabel.CENTER);
//        this.resultLabel.setVerticalTextPosition(JLabel.CENTER);
//
//        resultPanel.add(resultLabel);

        //======== Coordinates Panel ========

        JPanel coordinatesLabel = new JPanel(new GridLayout(1,1,5,5));
        coordinatesLabel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        coordinatesLabel.add(new JLabel("Coordinates (lat, lon, elev):"));

        JPanel coordinatesPanel = new JPanel(new GridLayout(3, 2, 5, 5));
        coordinatesPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));


        JLabel latTextLabel = new JLabel("Latitude: ");

        // gnorman note:
        // Create a post-validation formatter that will toss out non-double input
        // However this doesn't prevent bad input in real time the way a mask-formatter does
        NumberFormat format = DecimalFormat.getInstance();
        format.setMaximumIntegerDigits(2);
        format.setMinimumFractionDigits(0);
        format.setMaximumFractionDigits(10);
        format.setRoundingMode(RoundingMode.HALF_UP);

        latTextField = new JFormattedTextField(format);
        latTextField.setColumns(5);
//        latTextField.setDocument(newDocFilter());

        latTextField.addActionListener(event -> {
            String latInput = latTextField.getText();
            latLocation = Double.parseDouble(latInput);
        });

        JLabel lonTextLabel = new JLabel("Longitude: ");

        format.setMaximumIntegerDigits(3);
        format.setMinimumFractionDigits(0);
        format.setMaximumFractionDigits(10);
        format.setRoundingMode(RoundingMode.HALF_UP);

        lonTextField = new JFormattedTextField(format);
        lonTextField.setColumns(5);
//        lonTextField.setDocument(newDocFilter());

        lonTextField.addActionListener(event -> {
            String latInput = lonTextField.getText();
            lonLocation = Double.parseDouble(latInput);
        });

        JLabel elevTextLabel = new JLabel("Elevation: ");

        format.setMaximumIntegerDigits(5);
        format.setMinimumFractionDigits(0);
        format.setMaximumFractionDigits(10);
        format.setRoundingMode(RoundingMode.HALF_UP);

        elevTextField = new JFormattedTextField(format);
        elevTextField.setColumns(5);
//        elevTextField.setDocument(newDocFilter());

        elevTextField.addActionListener(event -> {
            String latInput = elevTextField.getText();
            elevLocation = Double.parseDouble(latInput);
        });
        coordinatesPanel.add(latTextLabel);
        coordinatesPanel.add(latTextField);
        coordinatesPanel.add(lonTextLabel);
        coordinatesPanel.add(lonTextField);
        coordinatesPanel.add(elevTextLabel);
        coordinatesPanel.add(elevTextField);


        //======== Label Panel ========  
        JPanel labelPanel = new JPanel(new GridLayout(1, 2, 5, 5));
        labelPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        labelPanel.add(new JLabel("Label:"));
        labelTextField = new JTextField();
        labelTextField.addActionListener(event -> {
            String labelInput = labelTextField.getText();
            placemark.setLabelText(labelInput);
        });
        labelPanel.add(labelTextField);
              
        //======== Scale Panel ========  
        JPanel scalePanel = new JPanel(new GridLayout(1, 2, 5, 5));
        scalePanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        scalePanel.add(new JLabel("Scale (1 is default):"));

        // Setting default scale to 1.0
        attrs.setScale(1.0);

        format.setMaximumIntegerDigits(2);
        format.setMinimumFractionDigits(0);
        format.setMaximumFractionDigits(10);
        format.setRoundingMode(RoundingMode.HALF_UP);

        scaleTextField = new JFormattedTextField(format);

        scaleTextField.addActionListener(event -> {
           String scaleInput = scaleTextField.getText();
           double scale = Double.parseDouble(scaleInput);
           attrs.setScale(scale);
        });
        scalePanel.add(scaleTextField);           

        //======== Check Boxes Panel ========  
        JPanel checkPanel = new JPanel(new GridLayout(1, 2, 2, 2));
        checkPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));

        showLabelCheck = new JCheckBox("Label");
        showLabelCheck.setSelected(true);
        showLabelCheck.addActionListener((ActionEvent event) ->
        {
            JCheckBox cb = (JCheckBox) event.getSource();
            wwd.redraw();
        });
        checkPanel.add(showLabelCheck);

        //======== Label Color Button ========  
        labelColorButton = new JButton("Label");
        labelColorButton.addActionListener((ActionEvent event) ->
        {
            Color c = JColorChooser.showDialog(colorPanel,
                    "Choose a color...", ((JButton) event.getSource()).getBackground());
            if (c != null)
            {
                ((JButton) event.getSource()).setBackground(c);
            }
        });
        colorPanel.add(labelColorButton);

        //======== Action Buttons ========  
        JPanel buttonPanel = new JPanel(new GridLayout(1, 2, 5, 5));
        buttonPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        addButton = new JButton("Add Placemark");

        addButton.addActionListener((ActionEvent actionEvent) ->
        {
            updateCoordinates();
            placemark.setAttributes(attrs);

            if(validateLatLongElev(latLocation, lonLocation, elevLocation)){
                placemark.setPosition(Position.fromDegrees(latLocation, lonLocation, elevLocation));
                layer.addRenderable(placemark);
                getWwd().getModel().getLayers().add(layer);

                // Fly to new Placemark
                View view = wwd.getView();
                double distance = view.getCenterPoint().distanceTo3(view.getEyePoint());
                view.goTo(placemark.getPosition(), distance);
            }

        });
        buttonPanel.add(addButton);
        addButton.setEnabled(true);

        viewButton = new JButton("View");
        viewButton.addActionListener((ActionEvent actionEvent) ->
        {
        });
        buttonPanel.add(viewButton);
        viewButton.setEnabled(false);


        //======== Outer Panel ======== 
        JPanel outerPanel = new JPanel();
        outerPanel.setLayout(new BoxLayout(outerPanel, BoxLayout.Y_AXIS));
        // Add the border padding in the dialog
        outerPanel.setBorder(new CompoundBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10), new TitledBorder("Point Placemarks")));
        outerPanel.setToolTipText("Create point placemarks on the globe");
        outerPanel.add(colorPanel);
        outerPanel.add(colorPanel);
        outerPanel.add(coordinatesLabel);
        outerPanel.add(coordinatesPanel);
//        outerPanel.add(resultPanel);
        outerPanel.add(labelPanel);
        outerPanel.add(scalePanel);
        outerPanel.add(checkPanel);
        outerPanel.add(buttonPanel);

        this.add(outerPanel, BorderLayout.NORTH);
    }

    private void updateCoordinates()
    {
        latLocation = Double.parseDouble(latTextField.getText());
        lonLocation = Double.parseDouble(lonTextField.getText());
        elevLocation = Double.parseDouble(elevTextField.getText());
        placemark.setLabelText(labelTextField.getText());
    }

    private boolean validateLatLongElev(double latLocation, double lonLocation, double elevLocation)
    {
        if(!(Math.abs(latLocation) <= 90)) {
            showMessageDialog(null, "Invalid Latitude Value: "
                    + latTextField.getText()
                    + "\n"
                    + "Usage:"
                    + "-90°<= Latitude <=90°"
                 );
            return false;
        } else if (!(Math.abs(lonLocation) <= 90)){
            showMessageDialog(null, "Invalid Longitude Value"
                + lonTextField.getText()
                + "\n"
                + "Usage:"
                + "-180°<= Longitude <=180°"
            );
            return false;
        } else if (!(Math.abs(elevLocation) < 100000)){
            showMessageDialog(null, "Invalid Elevation Value"
                + elevTextField.getText()
                + "\n"
                + "Usage:"
                + "-100000km < Elevation < 100000km"
            );
            return false;
        } else {
            return true;
        }
    }

    private PlainDocument newDocFilter()
    {
        PlainDocument doc = new PlainDocument();
        doc.setDocumentFilter(new DocumentFilter() {
            @Override
            public void insertString(FilterBypass fb, int off, String str, AttributeSet attr)
                throws BadLocationException
            {
                fb.insertString(off, str.replaceAll("\\D++", ""), attr);  // remove non-digits
            }
            @Override
            public void replace(FilterBypass fb, int off, int len, String str, AttributeSet attr)
                throws BadLocationException
            {
                fb.replace(off, len, str.replaceAll("\\D++", ""), attr);  // remove non-digits
            }
        });
        return doc;
    }

    public WorldWindow getWwd()
    {
        return this.wwd;
    }

    public void setWwd(WorldWindow wwd)
    {
        this.wwd = wwd;
    }
}
