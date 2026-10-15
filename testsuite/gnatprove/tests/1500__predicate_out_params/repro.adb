package body Repro with SPARK_Mode is

   ----------------------
   -- Grow_Array_First --
   ----------------------

   procedure Grow_Array_First (V : in out Vector) is
   begin
      Set_Array_First (V.Data, V.Last, 2);
   end Grow_Array_First;

   ---------------------
   -- Grow_Last_First --
   ---------------------

   procedure Grow_Last_First (V : in out Vector) is
   begin
      Set_Last_First (V.Last, V.Data, 2);
   end Grow_Last_First;

   ---------------------
   -- Set_Array_First --
   ---------------------

   procedure Set_Array_First
     (Data : in out Array_Type;
      Last : in out Length_Type;
      New_Last : Length_Type) is
   begin
      if New_Last >= 1 then
         Data (1).Value := 0;
      end if;
      if New_Last = 2 then
         Data (2).Value := 0;
      end if;
      Last := New_Last;
   end Set_Array_First;

   --------------------
   -- Set_Last_First --
   --------------------

   procedure Set_Last_First
     (Last : in out Length_Type;
      Data : in out Array_Type;
      New_Last : Length_Type) is
   begin
      if New_Last >= 1 then
         Data (1).Value := 0;
      end if;
      if New_Last = 2 then
         Data (2).Value := 0;
      end if;
      Last := New_Last;
   end Set_Last_First;

   ------------------------
   -- Shrink_Array_First --
   ------------------------

   procedure Shrink_Array_First (V : in out Vector) is
   begin
      Set_Array_First (V.Data, V.Last, 0);
   end Shrink_Array_First;

   -----------------------
   -- Shrink_Last_First --
   -----------------------

   procedure Shrink_Last_First (V : in out Vector) is
   begin
      Set_Last_First (V.Last, V.Data, 0);
   end Shrink_Last_First;
end Repro;
