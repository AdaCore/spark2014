with Types; use Types;
with P_List; use P_List; pragma Elaborate_All (P_List);
with P_U_Parent; use P_U_Parent;
with Ada.Text_IO; use Ada.Text_IO;

package body Run
with SPARK_Mode
is

   List : T_List := Init;

   procedure Compute_List;
   procedure Print;

   procedure Compute_List is
   begin
      for I in List'Range loop
         List (I).Compute;
      end loop;
   end Compute_List;

   procedure Print with SPARK_Mode => Off is
   begin
      Put_Line ("----");
      for I in List'Range loop
         Put_Line (T_Index'Image (I) & " => " & T0'Image (List (I).Get_X0));
      end loop;
      Put_Line ("----");
   end Print;

   procedure Run is
   begin
      for I in 1 .. 5 loop
         Compute_List;
         Print;
      end loop;
   end Run;

end Run;
