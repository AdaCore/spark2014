------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - E X P R - A G G R E G A T E S            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2023-2025, AdaCore                     --
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

with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;

package Gnat2Why.Expr.Aggregates is

   function Generate_VCs_For_Aggregate_Annotation
     (E : Type_Kind_Id) return W_Prog_Id
   with Pre => Has_Aggregate_Annotation (E);
   --  Generate checks for the initialization and the preservation of the
   --  invariants used to model aggregates.

   function Transform_Container_Aggregate
     (Expr : Node_Id; Params : Transformation_Params; Domain : EW_Domain)
      return W_Expr_Id;
   --  Generate the translation of a container aggregate. It is done similarly
   --  to array aggregates. A logic function is generated along with an axiom,
   --  and the aggregate is translated as a function call.

   function Transform_Deep_Delta_Aggregate
     (Expr : Node_Id; Domain : EW_Domain; Params : Transformation_Params)
      return W_Expr_Id;
   --  Transform a deep delta aggregate. It is translated directly as a record
   --  update if it contains only record components. Otherwise, a logic
   --  function is generated along with an axiom, and the aggregate is
   --  translated as a function call.

end Gnat2Why.Expr.Aggregates;
