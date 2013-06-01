------------------------------------------------------------------------------
--                                                                          --
--                            J S O N _ T R E E                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
--                                                                          --
-- gnatmerge is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatmerge is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Asis; use Asis;

package Json_Tree is

   procedure Insert (Kind : Declaration_Kinds; Kind_Name : String);

   procedure Iterate
     (Process : not null access procedure
        (Kind : String;
         Name : String;
         Sloc : String;
         Low  : String;
         High : String));

   procedure Open (File_Name : String);

   procedure Close;

end Json_Tree;
