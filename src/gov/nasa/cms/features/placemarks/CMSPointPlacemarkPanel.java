/*
 * Copyright (C) 2021 United States Government as represented by the Administrator of the
 * National Aeronautics and Space Administration.
 * All Rights Reserved.
 */
package gov.nasa.cms.features.placemarks;

import gov.nasa.cms.CelestialMapper;
import gov.nasa.cms.features.coordinates.*;
import gov.nasa.worldwind.View;
import gov.nasa.worldwind.*;
import gov.nasa.worldwind.avlist.AVKey;
import gov.nasa.worldwind.cache.BasicMemoryCache;
import gov.nasa.worldwind.geom.*;
import gov.nasa.worldwind.geom.coords.UTMCoord;
import gov.nasa.worldwind.layers.RenderableLayer;
import gov.nasa.worldwind.render.*;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.table.*;
import java.awt.*;
import java.awt.event.*;
import java.math.RoundingMode;
import java.text.*;
import java.util.*;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.*;

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

    private final CelestialMapper cms;
    private WorldWindow wwd;

    private JComboBox colorCombo;
    private JComboBox labelCombo;
    private JFormattedTextField latTextField;
    private JFormattedTextField lonTextField;
    private JFormattedTextField elevTextField;
    private JTextField labelTextField;
    private JFormattedTextField scaleTextField;
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
    private ArrayList <PointPlacemark> placemarkList;
    private PointPlacemarksTableModel placemarkTableModel;
    private JDialog placemarkTableDialog;
    private boolean isTableOpen;
    private double scale;
    private JTable table;
    private ArrayList<PointPlacemark> pointPlacemarkArrayList;
    private ArrayList<Map> mapArrayList = new ArrayList<>();
    private static int idCount = 0;
    private CMSWWOUnitsFormat unitsFormat;
    private DefaultTableModel model;
    private ArrayList pmPropertiesArrayList;

    public CMSPointPlacemarkPanel(WorldWindow wwdObject, CelestialMapper cms)
    {
        super(new BorderLayout());
        this.wwd = wwdObject;
        this.cms = cms;
        
        JPanel mainPanel = new JPanel();
        mainPanel.setOpaque(false);
        this.makePanel();
    }

    private void makePanel()
    {
        placemark = new PointPlacemark(Position.fromDegrees(0, 0, 1e4));
        layer = new RenderableLayer();
        layer.setName("User Added Placemarks");
        attrs = new PointPlacemarkAttributes();
        placemarkList = new ArrayList();
        pmPropertiesArrayList = new ArrayList();
        pointPlacemarkArrayList = new ArrayList<>();
//        placemarkTableModel = new PointPlacemarksTableModel();
//        placemarkTableDialog = createPlaceMarksTable();
        table = new JTable();
        configurePositionsTable(table);
        placemarkTableDialog = createPlaceMarksTable();
        
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
        attrs.setLineMaterial(Material.RED);

        colorCombo.addActionListener((ActionEvent event) ->
        {
            String item = (String) ((JComboBox) event.getSource()).getSelectedItem();
            if (item != null)
            {
                switch (item)
                {
                    case "Red":
                        attrs.setImageAddress("images/pushpins/plain-red.png");
                        attrs.setLineMaterial(Material.RED);
                        break;
                    case "Orange":
                        attrs.setImageAddress("images/pushpins/plain-orange.png");
                        attrs.setLineMaterial(Material.ORANGE);
                        break;
                    case "Yellow":
                        attrs.setImageAddress("images/pushpins/plain-yellow.png");
                        attrs.setLineMaterial(Material.YELLOW);
                        break;
                    case "Green":
                        attrs.setImageAddress("images/pushpins/plain-green.png");
                        attrs.setLineMaterial(Material.GREEN);
                        break;
                    case "Blue":
                        attrs.setImageAddress("images/pushpins/plain-blue.png");
                        attrs.setLineMaterial(Material.BLUE);
                        break;
                    case "Purple":
                        attrs.setImageAddress("images/pushpins/plain-purple.png");
                        attrs.setLineMaterial(new Material(new Color(102,0,153)));
                        break;
                    case "White":
                        attrs.setImageAddress("images/pushpins/plain-white.png");
                        attrs.setLineMaterial(Material.WHITE);
                        break;
                    case "Black":
                        attrs.setImageAddress("images/pushpins/plain-black.png");
                        attrs.setLineMaterial(Material.BLACK);
                        break;
                    case "Gray":
                        attrs.setImageAddress("images/pushpins/plain-gray.png");
                        attrs.setLineMaterial(Material.GRAY);
                        break;
                    default:
                        break;
                }
            } else {
                attrs.setImageAddress("images/pushpins/plain-red.png");
                attrs.setLineMaterial(Material.RED);
            }
        });
        colorPanel.add(colorCombo);
        
        JPanel labelColorPanel = new JPanel(new GridLayout(1, 2, 5, 5));
        labelColorPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        labelColorPanel.add(new JLabel("Label Color:"));
        labelCombo = new JComboBox<>(new String[]
        {
            "White", "Blue", "Black", "Red", "Orange", "Yellow", "Green", "Purple"
        });
        labelCombo.setSelectedIndex(0);
        attrs.setLabelColor("ffffffff"); // White is default
        
        labelCombo.addActionListener((ActionEvent event) ->
        {
            String item = (String) ((JComboBox) event.getSource()).getSelectedItem();
            if (item != null)
            {
                switch (item)
                {
                    case "White":
                        attrs.setLabelColor("ffffffff");
                        break;
                    case "Blue":
                        attrs.setLabelColor("ffff0000");
                        break;
                    case "Black":
                        attrs.setLabelColor("ff000000");
                        break;
                    case "Red":
                        attrs.setLabelColor("ff000000");
                        break;
                    case "Orange":
                        attrs.setLabelColor("f0000000");
                        break;
                    case "Yellow":
                        attrs.setLabelColor("ff000000");
                        break;
                    case "Green":
                        attrs.setLabelColor("ff000000");
                        break;                 
                    case "Purple":
                        attrs.setLabelColor("ff000000");
                        break;         
                    default:
                        break;
                }
            }
        }); 
        labelColorPanel.add(labelCombo);

        //======== Coordinates Panel ========
        JPanel coordinatesLabel = new JPanel(new GridLayout(1,1,5,5));
        coordinatesLabel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        coordinatesLabel.add(new JLabel("Coordinates (lat, lon, elev):"));

        JPanel coordinatesPanel = new JPanel(new GridLayout(3, 2, 5, 5));
        coordinatesPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));


        JLabel latTextLabel = new JLabel("Latitude: ");

        // gnorman note:
        // Number creates Format a post-validation formatter that will toss out non-double input
        // However this doesn't prevent bad input in real time the way a mask-formatter does
        NumberFormat latFormat = DecimalFormat.getInstance();
        latFormat.setMaximumIntegerDigits(2);
        latFormat.setMinimumFractionDigits(0);
        latFormat.setMaximumFractionDigits(10);
        latFormat.setRoundingMode(RoundingMode.HALF_UP);

        latTextField = new JFormattedTextField(latFormat);
        latTextField.setColumns(5);

        latTextField.addActionListener(event -> {
            String latInput = latTextField.getText();
            latLocation = Double.parseDouble(latInput);
        });

        JLabel lonTextLabel = new JLabel("Longitude: ");

        NumberFormat lonFormat = DecimalFormat.getInstance();
        lonFormat.setMaximumIntegerDigits(3);
        lonFormat.setMinimumFractionDigits(0);
        lonFormat.setMaximumFractionDigits(10);
        lonFormat.setRoundingMode(RoundingMode.HALF_UP);

        lonTextField = new JFormattedTextField(lonFormat);
        lonTextField.setColumns(5);

        lonTextField.addActionListener(event -> {
            String latInput = lonTextField.getText();
            lonLocation = Double.parseDouble(latInput);
        });

        JLabel elevTextLabel = new JLabel("Elevation (km): ");

        NumberFormat elevFormat = DecimalFormat.getInstance();
        elevFormat.setMaximumIntegerDigits(5);
        elevFormat.setMinimumFractionDigits(0);
        elevFormat.setMaximumFractionDigits(10);
        elevFormat.setRoundingMode(RoundingMode.HALF_UP);

        elevTextField = new JFormattedTextField(elevFormat);
        elevTextField.setColumns(5);

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
        scale = 1.0;
        attrs.setScale(scale);

        NumberFormat scaleFormat = DecimalFormat.getInstance();
        scaleFormat.setMaximumIntegerDigits(2);
        scaleFormat.setMinimumFractionDigits(0);
        scaleFormat.setMaximumFractionDigits(10);
        scaleFormat.setRoundingMode(RoundingMode.HALF_UP);

        scaleTextField = new JFormattedTextField(scaleFormat);

        scaleTextField.addActionListener(event -> {
            // Update scale
            String scaleInput = String.valueOf(scaleTextField.getValue());
            if(scaleInput.equals("") || scaleInput.isEmpty()){
                scaleTextField.setValue(null);
                scale = 1.0;
            } else {
                scale = Double.parseDouble(scaleInput);
            }
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
            showLabelCheck.setEnabled(cb.isEnabled());
            wwd.redraw();
        });
        checkPanel.add(showLabelCheck);

        //======== Action Buttons ========  
        JPanel buttonPanel = new JPanel(new GridLayout(1, 2, 5, 5));
        buttonPanel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));
        addButton = new JButton("Add Placemark");

        addButton.addActionListener((ActionEvent actionEvent) ->
        {
            updateCoordinates();
            attrs.setImageOffset(new Offset(19d, 8d, AVKey.PIXELS, AVKey.PIXELS));
            attrs.setLabelOffset(new Offset(0.9d, 0.6d, AVKey.FRACTION, AVKey.FRACTION));
            attrs.setLineWidth(2d);
            attrs.setScale(scale);

//            System.out.println(attrs.getScale());

            placemark.setAttributes(attrs);

            if(validateLatLongElev(latLocation, lonLocation, elevLocation))
            {
                placemark.setPosition(Position.fromDegrees(latLocation, lonLocation, elevLocation * 1000));

                PointPlacemark validPlacemark = new PointPlacemark(placemark.getPosition());
                validPlacemark.setAttributes(new PointPlacemarkAttributes(placemark.getAttributes()));
                System.out.println(validPlacemark.getAttributes().getScale());
                validPlacemark.setLabelText(placemark.getLabelText());
                validPlacemark.setLineEnabled(true);
                validPlacemark.setAltitudeMode(WorldWind.RELATIVE_TO_GROUND);
//                placemarkList.add(validPlacemark);

//                placemarkTableModel.addEntry(validPlacemark);
//                placemarkTableModel.addRow();7
                addPointPlacemarkRow(validPlacemark);

                layer.addRenderable(validPlacemark);
                getWwd().getModel().getLayers().add(layer);
                wwd.redraw();

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
            this.isTableOpen = !isTableOpen;
            if(isTableOpen){
                setTableVisible(true);
            }
            else
            {
                setTableVisible(false);
            }

            if(!placemarkList.isEmpty()){
                AtomicInteger i = new AtomicInteger(0);
                placemarkList.forEach((e) -> {System.out.println(i + ": " + e.getLabelText()); i.addAndGet(1);});
            }
        });
        buttonPanel.add(viewButton);
        viewButton.setEnabled(true);


        //======== Outer Panel ======== 
        JPanel outerPanel = new JPanel();
        outerPanel.setLayout(new BoxLayout(outerPanel, BoxLayout.Y_AXIS));
        // Add the border padding in the dialog
        outerPanel.setBorder(new CompoundBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10), new TitledBorder("Point Placemarks")));
        outerPanel.setToolTipText("Create point placemarks on the globe");
        outerPanel.add(colorPanel);
        outerPanel.add(labelColorPanel);
        outerPanel.add(coordinatesLabel);
        outerPanel.add(coordinatesPanel);
        outerPanel.add(labelPanel);
        outerPanel.add(scalePanel);
        outerPanel.add(checkPanel);
        outerPanel.add(buttonPanel);

        this.add(outerPanel, BorderLayout.NORTH);
    }

    private void configurePositionsTable(JTable table)
    {
        // This defines the Header row for the table
        String[] COLUMN_NAMES = new String[] {"Id", "Label", "Lat", "Long", "Elev", "Scale"};

        // Mismatch between column positions and these declared classes will cause an untraceable
        // runtime exception!!
//        Class[] columnClass = new Class[] {
//            Integer.class, String.class, Double.class,Double.class,Double.class,Double.class
//        };
        Class[] columnClass = new Class[] {
            String.class, String.class, String.class,String.class,String.class,String.class
        };
        
        // This defines the table using the much easier to use DefaultTableModel
        // and initializes it to be empty
        model = new DefaultTableModel(COLUMN_NAMES, 0) {

            // Right now we are only inserting Strings into the table
            // so this Run Time method may not need to be overridden
            @Override
            public Class<?> getColumnClass(int columnIndex) {
                Class cls = String.class;
                cls = columnClass[columnIndex];
                return cls;
            }

            @Override
            public boolean isCellEditable(int row, int column) {
                //all cells false
                return false;
            }
        };

        table.setModel(model);
    }

    public void addPointPlacemarkRow(PointPlacemark pm){

            // First add placemark to internal ArrayList
            pointPlacemarkArrayList.add(pm);

            // Then extract the properties of the placemark as strings for display in the table
            // TODO - Capture elevation on the surface vs the relative elevation above the surface
            Position currentPosition = pm.getPosition();

            var id = String.valueOf(++idCount);
            var label = pm.getLabelText();
            var latitude = String.valueOf(currentPosition.getLatitude()).trim();
            var longitude = String.valueOf(currentPosition.getLongitude()).trim();
            var elevation = String.valueOf(currentPosition.getElevation()).trim();
            var scale = String.valueOf(pm.getAttributes().getScale());

            var list = List.of(id, label, latitude, longitude, elevation, scale);
            pmPropertiesArrayList.add(list);
            Vector vec = new Vector(list);
            model.addRow(vec);
    }

    private JDialog createPlaceMarksTable()
    {
        JDialog dialog = new JDialog(cms);
        Rectangle bounds = cms.getBounds();
        dialog.getContentPane().setLayout(new BorderLayout());
        dialog.setTitle("Point Placemarks");
        // Set the location and resizable to false
        dialog.setLocation(bounds.x + 100, bounds.y + 100);
        dialog.setResizable(true);
        // Add the tabbedPane to the dialog
//        dialog.getContentPane().add(new JScrollPane(new JTable(placemarkTableModel)), BorderLayout.CENTER);
        dialog.getContentPane().add(new JScrollPane(table), BorderLayout.CENTER);
        dialog.pack();
        return dialog;
    }

    private void updateCoordinates()
    {
        if(!latTextField.getText().isEmpty()){
            latLocation = Double.parseDouble(latTextField.getText());
        } else {
            latLocation = 0.0;
            latTextField.setValue(latLocation);
        }

        if(!lonTextField.getText().isEmpty()){
            lonLocation = Double.parseDouble(lonTextField.getText());
        } else {
            lonLocation = 0.0;
            lonTextField.setValue(lonLocation);
        }

        if(!elevTextField.getText().isEmpty()){
            elevLocation = Double.parseDouble(elevTextField.getText());
        } else {
            elevLocation = 0.0;
            elevTextField.setValue(elevLocation);
        }

        if(!scaleTextField.getText().isEmpty() && !scaleTextField.getText().equals("")){
            scale = Double.parseDouble(scaleTextField.getText());
        } else {
            scale = 1.0;
            scaleTextField.setValue(null);
        }

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
        } else if (!(Math.abs(lonLocation) <= 180)){
            showMessageDialog(null, "Invalid Longitude Value"
                + lonTextField.getText()
                + "\n"
                + "Usage:"
                + "-180°<= Longitude <=180°"
            );
            return false;
        } else if (!(Math.abs(elevLocation) < (100000))){
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

    public WorldWindow getWwd()
    {
        return this.wwd;
    }

    public void setTableVisible(boolean visible)
    {
        placemarkTableDialog.setVisible(visible);
    }
}
