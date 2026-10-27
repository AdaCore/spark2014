procedure Boxed_Records with SPARK_Mode is
   type Rec (D : Boolean := False) is record
      F : Integer := 42;
   end record with Relaxed_Initialization;
   type Arr is array (1 .. 2) of Rec;
   function Defaults return Arr is ((others => <>));

   type Partial (D : Boolean := True) is record
      F : Integer := 7;
      G : Integer;
   end record with Relaxed_Initialization;
   type Partial_Arr is array (1 .. 2) of Partial;
   function Partial_Defaults return Partial_Arr is ((others => <>));

   X : Arr := Defaults;
   Y : Partial_Arr := Partial_Defaults;
begin
   pragma Assert (X (1).D = False);
   pragma Assert (X (1).F = 42);
   pragma Assert (X (2)'Initialized);
   pragma Assert (Y (1).D);
   pragma Assert (Y (1).F = 7);
   --  A box initializes the discriminant and defaulted field, not G.
   pragma Assert (Y (2).G'Initialized); --@ASSERT:FAIL
end Boxed_Records;
