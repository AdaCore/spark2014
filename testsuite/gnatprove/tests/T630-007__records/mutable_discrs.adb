with Ext;

procedure Mutable_Discrs with SPARK_Mode is
   type My_Rec (D : Boolean := True) is record
      F : Integer;
   end record;
   subtype S is My_Rec (True);

   function Id (X : Integer) return Integer is (X);

   type My_Array is array (Positive range <>) of Integer;
   subtype AS is My_Array (1 .. 2);
   C : constant Integer := Id (2);
   subtype AS_2 is My_Array (1 .. C);

   procedure Do_Something (X : in out S) with Import;
   procedure Do_Something_2 (X : in out My_Rec) with Import;
   procedure Do_Something_3 (X : in out AS_2) with Import;

   X : My_Rec := (D => True, F => 1);
   Y : S := (D => True, F => 1);
   A : AS := (others => 1);
   V1 : Ext.Nested.My_Rec := Ext.Vol;
   V2 : Ext.Nested.My_Rec := Ext.Vol;
begin
   Do_Something (X);
   pragma Assert (X.D);
   Do_Something_2 (Y);
   pragma Assert (Y.D);
   Do_Something_3 (A);
   pragma Assert (Ext.Nested.Same_Discrs (V1, V2)); --@ASSERT:FAIL
end Mutable_Discrs;
