// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 28 June 2008 at  0:23:49 PST by lamport  

package translation;

import java.io.File;
import java.net.URL;

import util.FileUtil;
import util.FilenameToStream;
import util.ToolIO;


/**
 * Defines a translation from names to NamedInputStream's that will be
 * used by most tools whose input comes from files.
 * @author simonzam Leslie Lamport, Simon Zambrovski
 * @version $Id: SimpleFilenameToStream.java 12969 2009-02-24 22:12:33Z simonzam $
 */
//SZ Feb 20, 2009: moved to util and fixed bugs

// If a file ``matching'' the module name is found then an instance of 
// a stream - NamedInputStream is returned.

// This code contains a special detector trace for the presence of a 
// newline in a string. This was a problem with earlier versions of java on PCs.


public class MySimpleFilenameToStream implements FilenameToStream {

  // SZ Feb 23, 2009:
  // used File.separator and File.pathSeparator instead
  // the character separating names of directories in the libraryPath    
  // private static String pathsep     = System.getProperty("path.separator"); 
  // the character separating names of directories in the libraryPath
  // private static String filesep     = System.getProperty("file.separator"); 
  
  
  private static String installationBasePath = getInstallationBasePath();
                                            // Find the absolute path in the file system where SANY is installed
  private static String[] libraryPaths = getLibraryPaths();
                                            // path of directories to be searched in order for the named file
  // Find the absolute path in the file system to the directory 
  // that is the base of the entire installation of tlaSANY; this path
  // must have separators appropriate to the Unix ('/') or Windows ('\') world.

  private static String getInstallationBasePath() {

    ClassLoader cl  = ClassLoader.getSystemClassLoader();

    // get a "file:" URL for the base directory for package tla2sany
    URL         url = cl.getResource("tla2sany");

    // Strip off the initial "file:" from the URL
    String      path =  url.toString().substring(5);

    // Strip off however many initial "/" characters are present in the URL
    while ( path.charAt(0) == '/' ) { path = path.substring(1); }

    // Prepend with the culturally-appropriate file separator character ('/' or '\')
    path = FileUtil.separator + path;

    // Change any '/'-characters to the culturally-appropriate file separator character
    path = path.replace('/', FileUtil.separatorChar );

    // Debug
    // System.out.println("Installation base path = " + path);

    return path;
  }

  private static String[] getLibraryPaths() {
    String[] res;
    String path = System.getProperty("TLA-Library");
    if (path == null) {
      res = new String[1];
      res[0] = installationBasePath + FileUtil.separator + "StandardModules" + FileUtil.separator;
    }
    else {
      String[] paths = path.split(FileUtil.pathSeparator);
      res = new String[paths.length+1];
      for(int i=0;i<paths.length;i++){
	res[i] = paths[i];
	if (!res[i].endsWith(FileUtil.separator)){
	  res[i] = res[i] + FileUtil.separator;
	}
      }
      res[paths.length] = installationBasePath + FileUtil.separator + "StandardModules" + FileUtil.separator;
    }
    return res;
  }
  
  /**
   *  From name, prepend path elements to try to find the actual
   *  file intended, and use the resulting fully-qualified name to initialize 
   *  the File.  The first fully-qualified name that refers to a file that actually
   *  exists is the File returned; but if none exists, the last one tried is returned 
   *  anyway.  Hence, the File object returned does not necessarily represent a file
   *  that actually exists in the file system.
   *  
   *  @param  module name, used as basis of path name to the file that should contain it
   */
  private final File locate(String name) 
  {

    String prefix      = "";                // directory to be prepended to file name before lookup

    File   sourceFile  = null;              // File object from fully-qualified name of file found by
                                            //   searching "libraryPath" for "name", as is done for PATHs and CLASSPATHs
 
    // The TLA standard modules are presumed to be in a directory tla2sany/StandardModules
    // i.e. a toplevel subdirectory of the main installation directory for SANY
    // We append the StandardModules director to the library path, so the user does
    // not have to do anything special and the standard modules are automatically accessible

    // Debug
    /*
    System.err.println("Installation base path = " + installationBasePath);
    for (int i=0;i<libraryPaths.length;i++)
    {
        System.err.println("libraryPaths = '" + libraryPaths[i] + "'");
    }
    */

    // This code ALWAYS looks in the current directory first for a file (and its capitalization
    // variants), regardless of what the TLA-Library property says the search path should be.
    /***********************************************************************
    * This was modified by LL on 14 May 2008 to change the way sourceFile  *
    * is obtained from sourceFileName.  See the comments for the userDir   *
    * field in util/ToolIO.                                                *
    ***********************************************************************/
    int idx = 0;
    while (true) 
    {
        if ((idx == 0) && (ToolIO.getUserDir() != null)) {
            sourceFile = new File(ToolIO.getUserDir(), name );
        }
        else 
        {
            sourceFile = new File( prefix + name );
        }
        // Debug
        // System.out.println("Looking for file " + sourceFile);
        if ( sourceFile.exists() )  break;
        if (idx >= libraryPaths.length) break;
        prefix = libraryPaths[idx++];
    } // end while

    return sourceFile;

  } // end locate()

  /**
   * Returns a file
   * obtained by some standard method from the string name.  For example,
   * resolve("Foo") might equal the file "/udir/luser/current/path/Foo.tla".
   * 
   * Returns null if the file does not exist
   */ 
  public File resolve(String name, boolean isModule)
  {
      // Strip off one NEWLINE and anything after it, if it is there
      int n;
      n = name.indexOf( '\n' );
      if ( n >= 0 ) {
          // SZ Feb 20, 2009: the message adjusted to what is actually done 
          ToolIO.out.println("*** Warning: module name '" + name + "' contained NEWLINE; "
                  + "Only the part before NEWLINE is considered.");
          name = name.substring( 0, n );     // Strip off the newline
      }
      String sourceFileName = null;
      // SZ Feb 20, 2009: 
      // if the name is a name of the module
      if (isModule) 
      {
          // SZ Feb 20, 2009: 
          // Make sure the file name ends with ".tla".
          if (name.toLowerCase().endsWith(".tla")) 
          {
              name = name.substring(0, name.length() - 4);
          }
          sourceFileName = name + ".tla";
      } else 
      {
          // SZ Feb 20, 2009: for other files 
          // leave the name untouched
          sourceFileName = name;
      }
      // identify the library property
      // extract substrings with getProperty("path.separator");
      // repeat search for each substring until found.
      // locate() the file corresponding to the sourceFileName
      return locate(sourceFileName);
  }

  

} // end class
