package R is
   type T is range 1 .. 10;

   type Rec is record
      F1 : Integer;
      F2 : Boolean;
   end record;

   type Arr is array (T) of Rec;

   Null_Arr : constant Arr := Arr'(others => Rec'(0, False));

   Arr_Obj : Arr := Null_Arr;

   V : T := 1;

   --  Renamings that involve prefixes of selected components.
   --  Needed to show that the traversal of the Name tree
   --  is correctly skipping over the Prefix nodes and finding
   --  the nested indexed components nodes.

   S1 : Integer renames Arr_Obj (1).F1; -- static index, Legal

   S2 : Integer renames Arr_Obj (V).F1; -- var index, Illegal

end R;
