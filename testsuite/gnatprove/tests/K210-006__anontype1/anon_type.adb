--  3.3.1 Object Declarations
--  3.3.1:
--  object_declaration ::=
--     defining_identifier_list : [aliased] [constant] subtype_indication [:= expression];
--   | defining_identifier_list : [aliased] [constant] access_definition [:= expression];
--   | defining_identifier_list : [aliased] [constant] array_type_definition [:= expression];
--   | single_task_declaration
--   | single_protected_declaration
--  3.3.1:
--  defining_identifier_list ::=
--   defining_identifier {, defining_identifier}

-- with Ada;

package body Anon_Type is
   function Increment (Var_In : in Integer) return Integer
   is
      --  Examples of constant declarations:
      Limit     : constant Integer := 10_000;
      --  Examples of subtype_indication:
      Var_Out   : Integer range 0 .. 10 := 0;
      --  Example of a range attribute reference
      --  Examples of subtype_indication with multiple definition:
      A, B      : Integer range -Limit .. +Limit;
      --  Examples of subtype_indication with An_Index_Constraint:
      Ten_Characters : String(1 .. 10) := (others => ' ');
      Board     : Vector(1 .. 5);
      --  Examples of array_type_definition
      My_Array1 : array (1.. 10) of Integer;
      My_Array2 : array (1.. 20) of Integer;
   begin
      Board := (others => 1.0);
      Var_Out := Var_In + (Var_Out + 1);
      return Var_Out;
   end Increment;
end Anon_Type;
