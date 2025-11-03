procedure P (C : Integer) with SPARK_Mode is
   type Dyn_Arr is array (1 .. C) of Integer;
   type Record_Holder is record
      C : Dyn_Arr;
   end record;
   type Array_Holder is array (1 .. 10) of aliased Record_Holder;

   procedure P1 is
      X : Dyn_Arr := (others => 1);
      Y : Integer
      with Import, Address => X'Address;
   begin
      null;
   end P1;

   procedure P2 is
      X : Record_Holder := (C => (others => 1));
      Y : Integer
      with Import, Address => X.C'Address;
   begin
      null;
   end P2;

   procedure P3 is
      X : Array_Holder := (1 .. 10 => (C => (others => 1)));
      Y : Integer
      with Import, Address => X (5)'Address;
   begin
      null;
   end P3;

   procedure P4 (D : Integer) is
      X : Array_Holder := (1 .. 10 => (C => (others => 1)));
      Y : Integer
      with Import, Address => X (D .. 5)'Address;
   begin
      null;
   end P4;
begin
   null;
end P;
