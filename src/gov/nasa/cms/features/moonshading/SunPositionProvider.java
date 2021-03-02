package gov.nasa.cms.features.moonshading;

import gov.nasa.worldwind.geom.LatLon;

/**
 * @author Michael de Hoog
 * @version $Id: SunPositionProvider.java 10406 2009-04-22 18:28:45Z patrickmurris $
 */
public interface SunPositionProvider {

    public LatLon getPosition();
    public void updateDateTime();
     public void updateCurrentDateTime();
}
