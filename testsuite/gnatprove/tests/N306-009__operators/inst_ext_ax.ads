with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Doubly_Linked_Lists;

package Inst_Ext_Ax with SPARK_Mode is
   package OK_Lists1 is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type => Natural);
   package OK_Lists2 is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type => Natural);

   subtype Int100 is Integer range 0 .. 100;
   subtype Int200 is Integer range 0 .. 200;

   generic
      with function Add (I1, I2 : Int100) return Int100;
   package My_Add is
      pragma Annotate (GNATprove, External_Axiomatization);
      function Add_Wrap (I1, I2 : Int100) return Int100 is
         (Add (I1, I2));
   end;

   generic
      with function Add (I1, I2 : Int100) return Int100;
      with function Add2 (I1, I2, I3 : Int200) return Int200;
   package My_Add2 is
      pragma Annotate (GNATprove, External_Axiomatization);
      function Add_Wrap (I1, I2 : Int100) return Int200 is
         (Add (I1, I2) + Add2(I1, I2, I1));
   end;

   function AddThree(A, B, C : Integer) return Integer is
      (A + B + C);

   package Bad_Add is new My_Add ("+"); --@RANGE_CHECK:FAIL
   package Bad_Add2 is new My_Add2 ("+", AddThree); --@RANGE_CHECK:FAIL
end;
