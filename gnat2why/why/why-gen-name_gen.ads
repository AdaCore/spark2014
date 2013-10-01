------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - G E N - N A M E _ G E N                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Namet;        use Namet;
with Types;        use Types;
with Why.Ids;      use Why.Ids;
with Why.Sinfo;    use Why.Sinfo;

package Why.Gen.Name_Gen is

   generic
      Domain    : EW_Domain;
      Prefix    : String;
      Suffix    : String;
      Separator : String := "___";
   package Arity_1 is
      function Id
        (Ada_Node : Node_Id;
         Name     : String)
        return W_Identifier_Id;

      function Id
        (Ada_Node : Node_Id;
         Name     : Name_Id)
        return W_Identifier_Id;

      function Id
        (Ada_Node : Node_Id;
         Name     : W_Identifier_Id)
        return W_Identifier_Id;

      function Id
        (Name : String)
        return W_Identifier_Id;

      function Id
        (Name : Name_Id)
        return W_Identifier_Id;

      function Id
        (Name : W_Identifier_Id)
        return W_Identifier_Id;
   end Arity_1;

   generic
      Domain    : EW_Domain;
      Prefix    : String;
      Middle    : String;
      Suffix    : String;
      Separator : String := "___";
   package Arity_2 is
      function Id
        (Ada_Node : Node_Id;
         L_Name   : String;
         R_Name   : String)
        return W_Identifier_Id;

      function Id
        (Ada_Node : Node_Id;
         L_Name   : Name_Id;
         R_Name   : Name_Id)
        return W_Identifier_Id;

      function Id
        (Ada_Node : Node_Id;
         L_Name   : W_Identifier_Id;
         R_Name   : W_Identifier_Id)
        return W_Identifier_Id;

      function Id
        (L_Name : String;
         R_Name : String)
        return W_Identifier_Id;

      function Id
        (L_Name : Name_Id;
         R_Name : Name_Id)
        return W_Identifier_Id;

      function Id
        (L_Name : W_Identifier_Id;
         R_Name : W_Identifier_Id)
        return W_Identifier_Id;
   end Arity_2;

end Why.Gen.Name_Gen;
