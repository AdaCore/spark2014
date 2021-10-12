------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                             S P A R K _ R A C                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2021, AdaCore                       --
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

with Ada.Containers;        use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Ordered_Maps;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Common_Containers;     use Common_Containers;
with Types;                 use Types;
with VC_Kinds;              use VC_Kinds;

package SPARK_RAC is

   type Result;
   --  Information about the termination of the RAC execution

   function RAC_Execute
     (E              : Entity_Id;
      Cntexmp        : Cntexample_File_Maps.Map := Cntexample_File_Maps.Empty;
      Do_Sideeffects : Boolean := False;
      Fuel           : Integer := -1;
      Stack_Height   : Integer := -1)
      return Result;
   --  Runtime assertion checking execution of subprogram E using the
   --  counterexample Cntexmp as an oracle for program parameters. When
   --  Do_Sideeffects is True, then builtins are interpreted with side effects.
   --  If Fuel is non-negative, it is decreased in the execution of every
   --  statement or expression, and the execution terminates as incomplete,
   --  when it reaches zero. If Stack_Height is non-zero the execution
   --  terminates as incomplete when the stack of calls to procedures or
   --  functions grows higher than this number. Raises RAC_Unexpected_Error
   --  when something unforeseen happens.

   type Value_Type is (Ty_Integer, Ty_Enum, Ty_Record, Ty_Array, Ty_String);
   --  The type of a value in the RAC engine

   type Value;
   --  A value in the RAC engine

   type Value_Access is access Value;
   --  A pointer to a value

   package Fields is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Value_Access, -- Access since value type is incomplete
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Fields of a record value

   package Values_Map is
      new Ada.Containers.Ordered_Maps
       (Key_Type     => Integer,
        Element_Type => Value_Access);
   --  Values for a one-dimensional array. Keys may be integers or positions
   --  for enum values.

   type Value (Ty : Value_Type := Ty_Integer) is record
      case Ty is
         when Ty_Integer =>
            Integer_Content : Big_Integer;
         when Ty_Enum =>
            Enum_Entity     : Entity_Id;
         when Ty_Record =>
            Record_Fields   : Fields.Map;
         when Ty_Array =>
            Array_First     : Big_Integer;
            Array_Last      : Big_Integer;
            Array_Values    : Values_Map.Map;
            Array_Others    : Value_Access;
            --  Sparse representation of array values following counterexample
            --  array values
         when Ty_String =>
            String_First    : Big_Integer;
            String_Content  : Unbounded_String;
      end case;
   end record;
   --  A value in the RAC engine

   type Opt_Value (Present : Boolean := False) is record
      case Present is
         when True =>
            Content : Value;
         when False =>
            null;
      end case;
   end record;
   --  An optional value in the RAC engine

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
            Res_Value   : Opt_Value;
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

   function "=" (V1, V2 : Value) return Boolean;
   --  Test equality of two values

   function To_String (V : Value) return String;

   function To_String (V : Opt_Value) return String;

   function To_String (Res : Result) return String;

   function Reason (Res : Result) return String is
     (case Res.Res_Kind is
         when Res_Incomplete | Res_Stuck | Res_Not_Executed =>
            To_String (Res.Res_Reason),
         when Res_Normal | Res_Failure                      =>
            "");
   --  Return the reason for a result ("" for failure and normal)

   function Do_RAC_Info return Boolean;

end SPARK_RAC;
