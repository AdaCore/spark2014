with Ada.Containers.Doubly_Linked_Lists;

procedure Loops is pragma SPARK_Mode (Off); --  standard lists
   subtype Small_Natural is Natural range 0 .. 5;

   subtype First_Dim is Positive range 1 .. 3;
   subtype Second_Dim is Positive range 1 .. 4;
   type Test_Array is array (First_Dim, Second_Dim) of Integer;

   package DLL is new Ada.Containers.Doubly_Linked_Lists (Integer, "=");

   Counter : Natural := 0;
   L       : DLL.List;
   TA      : Test_Array := (others => (others => 1234));

begin
   --  while Condition loop

   Loop1 : while Counter < 5 loop
      Counter := Counter + 1;
   end loop Loop1;

   --  for Def_Id in [reverse] Range loop

   Loop2 : for Index in 1 .. 5 loop
      Counter := Counter + 1;
   end loop Loop2;

   --  for Def_Id in [reverse] Discrete_Subtype_Indication loop

   Loop3 : for Index in Small_Natural loop
      Counter := Counter + 1;
   end loop Loop3;

   --  for Def_Id in [reverse] Iterator_Name loop

   --  expanded into:
   --     Loop4 : while DLL.Has_Element (Index) loop

   Loop4 : for Index in DLL.Iterate (L) loop
      Counter := Counter + 1;
   end loop Loop4;

   --  for Def_Id [: Subtype_Indication] of [reverse] Array_Name loop

   --  expanded into:
   --     Loop5 : for Temp1 in <first_dim_low> ... <first_dim_high> loop
   --        for Temp2 in <second_dim_low> .. <second_dim_high> loop

   Loop5 : for Index of TA loop
      Counter := Counter + 1;
   end loop Loop5;

   --  for Def_Id [: Subtype_Indication] of [reverse] Container_Name loop

   --  expanded into:
   --     Loop6 : while DLL.Has_Element (Temp_Iterator) loop

   Loop6 : for Index of L loop
      Counter := Counter + 1;
   end loop Loop6;

end Loops;
