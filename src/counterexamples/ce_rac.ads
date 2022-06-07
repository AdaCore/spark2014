------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                             S P A R K _ R A C                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2021-2022, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
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
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

--  This package implements small-step (normal) runtime-assertion checking
--  (RAC) for SPARK to check counterexamples.

with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with CE_Values;             use CE_Values;
with SPARK_Atree.Entities;  use SPARK_Atree.Entities;
with Types;                 use Types;
with VC_Kinds;              use VC_Kinds;

package CE_RAC is

   type Result;
   --  Information about the termination of the RAC execution

   type Fuel_Type is new Integer;

   type Fuel_Access is access Fuel_Type;
   --  If the fuzzer is used, the fuel must be shared and modified by each call
   --  to the small-step RAC.

   procedure Check_Fuel_Decrease (Fuel : Fuel_Access);
   --  Check fuel and decrease. Raise RAC_Incomplete when fuel becomes zero.
   --  Do nothing for negative values of Fuel.

   function Find_Binding (E : Entity_Id) return Value_Access;
   --  Find the binding of a variable in the context environment. If not found,
   --  it is assumed to be a global constant and initialised as it.

   procedure Get_Integer_Type_Bounds
     (Ty       :     Entity_Id;
      Fst, Lst : out Big_Integer)
   with
     Pre => Is_Integer_Type (Ty);
   --  Write the first and last value of an integer type Ty in Fst and Lst

   function Integer_Value (I : Big_Integer; N : Node_Id) return Value_Type;
   --  Construct an integer value after checking against type bounds or
   --  applying modulo for type Etype (N), signaling errors for node N.

   function RAC_Execute
     (E              : Entity_Id;
      Cntexmp        : Cntexample_File_Maps.Map := Cntexample_File_Maps.Empty;
      Do_Sideeffects : Boolean := False;
      Fuel           : Fuel_Access := null;
      Stack_Height   : Integer := -1;
      Use_Fuzzing    : Boolean := False)
      return Result;
   --  Runtime assertion checking execution of subprogram E using the
   --  counterexample Cntexmp as an oracle for program parameters. When
   --  Do_Sideeffects is True, then builtins are interpreted with side effects.
   --  If Fuel is non-negative, it is decreased in the execution of every
   --  statement or expression, and the execution terminates as incomplete,
   --  when it reaches zero. If Stack_Height is non-zero the execution
   --  terminates as incomplete when the stack of calls to procedures or
   --  functions grows higher than this number. Raises RAC_Unexpected_Error
   --  when something unforeseen happens. If Use_Fuzzing is set to True,
   --  randomly chosen values will be used for the program's variables rather
   --  than the values provided by the counterexample.

   procedure RAC_Stuck (Reason : String) with No_Return;
   --  Raise Exn_RAC_Stuck and set result, i.e. the RAC execution failed
   --  due to a false assumption.

   type Result_Kind is
     (Res_Normal,
      --  RAC execution terminated normally, without encountering an invalid
      --  check
      Res_Failure,
      --  RAC execution failed due to an invalid check
      Res_Incomplete,
      --  RAC execution could not be completed (e.g., missing implementation)
      Res_Stuck,
      --  RAC execution got stuck (e.g., invalid values in the counterexample)
      Res_Not_Executed
      --  RAC execution has not been requested
     );
   --  The different ways how the RAC execution can terminate

   type Result (Res_Kind : Result_Kind := Res_Not_Executed) is record
      case Res_Kind is
         when Res_Normal =>
            Res_Value   : Opt_Value_Type;
            --  The result value of toplevel RAC call
         when Res_Failure =>
            Res_Node    : Node_Id;
            --  The node of the check that failed (only set by RAC)
            Res_VC_Kind : VC_Kind;
            --  The VC kind that triggered the failure
            Res_VC_Id   : Natural := Natural'Last;
            --  The ID of the check that failed (not set by RAC)
         when Res_Incomplete
            | Res_Stuck
            | Res_Not_Executed
         =>
            Res_Reason  : Unbounded_String;
      end case;
   end record;

   RAC_Unexpected_Error : exception;
   --  Raised when something unforeseen happens, but not program or constraint
   --  error

   function To_String (Res : Result) return String;

   function Reason (Res : Result) return String is
     (case Res.Res_Kind is
         when Res_Incomplete | Res_Stuck | Res_Not_Executed =>
            To_String (Res.Res_Reason),
         when Res_Normal | Res_Failure                      =>
            "");
   --  Return the reason for a result ("" for failure and normal)

   function Do_RAC_Info return Boolean;

end CE_RAC;
