with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Doubly_Linked_Lists;

package Inst_Ext_Ax with SPARK_Mode is
   package OK_Lists1 is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type => Natural);
   package OK_Lists2 is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type => Natural, "=" => "=");

   subtype Int100 is Integer range 0 .. 100;

   generic
      with function Add (I1, I2 : Int100) return Int100;
   package My_Add is
      pragma Annotate (GNATprove, External_Axiomatization);
      function Add_Wrap (I1, I2 : Int100) return Int100 is
         (Add (I1, I2));
   end;

   package Bad_Add is new My_Add ("+"); --@RANGE_CHECK:FAIL
end;
