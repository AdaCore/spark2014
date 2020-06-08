------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            T E M P L A T E S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Outputs; use Outputs;

package Templates is
   --  This package provides some support for substitutions of patterns
   --  in template files.

   procedure Add
     (Pattern   : String;
      Generator : not null access procedure (O : in out Output_Record));
   --  Associate Pattern to Generator

   procedure Process (Filename : String);
   --  Open an output record for Filename and fill Filename using
   --  a template (whose name is Filename suffixed by --  "-tmpl");
   --  when reading the template, each occurence of Patterns in
   --  are replaced by the result of the execution of its associated
   --  generator.
   --
   --  Patterns are recognized by the following syntax:
   --
   --     _@My_Pattern@_
   --
   --  Each time such a pattern is found, the corresponding generator
   --  (registered by Add) is looked up; if not found, no substitution
   --  is done and a warning is issued. Otherwise, the indentation level
   --  of the output is set the indentation level of the pattern and
   --  the generator is called to operate the substitution.

end Templates;
