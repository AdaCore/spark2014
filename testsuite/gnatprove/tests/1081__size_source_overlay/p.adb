procedure P with SPARK_Mode is
   type R2 is record
      X, Y : Character;
   end record;
   type R2b is record
      X, Y : Character;
      B    : Boolean;
   end record
   with Size => 17, Object_Size => 24;
   for R2b use record
       X at 0 range 0 .. 7;
       Y at 0 range 8 .. 15;
       B at 0 range 16 .. 16;
      end record;
   type R3 is record
      X, Y, Z : Character;
   end record;

   procedure Test_Object_Size_Check_On_Source_1 is
      Z : R3 := ('a', 'b', 'c');
      X : R2
      with Import, Address => Z'Address, Size => 24;  --  Should be rejected, X has unused bits
   begin
      null;
   end Test_Object_Size_Check_On_Source_1;

   procedure Test_Object_Size_Check_On_Source_2 is
      Z : constant R3 := ('a', 'b', 'c');
      X : constant R2
      with Import, Address => Z'Address, Size => 24;
      Y : constant R3
      with Import, Address => X'Address;  --  Should be rejected, X has unused bits
   begin
      null;
   end Test_Object_Size_Check_On_Source_2;

   procedure Test_Object_Size_Check_On_Source_3 is
      Z : R3 := ('a', 'b', 'c');
      X : R2b
      with Import, Address => Z'Address;  --  Should be rejected, X has unused bits
   begin
      null;
   end Test_Object_Size_Check_On_Source_3;

   procedure Test_Object_Size_Check_On_Source_4 is
      Z : constant R3 := ('a', 'b', 'c');
      X : constant R2b
      with Import, Address => Z'Address;
      Y : constant R3
      with
        Import,
        Address => X'Address;  --  Should be rejected, X has unused bits
   begin
      null;
   end Test_Object_Size_Check_On_Source_4;

   procedure Test_Object_Size_Check_On_Source_5 is
      Z : R2 := ('a', 'b');
      X : Character with Size => 16, Import, Address => Z'Address; --  X might have invalid values, but it does not have unused bits
   begin
      null;
   end Test_Object_Size_Check_On_Source_5;

   procedure Test_Object_Size_Check_On_Source_6 is
      Z : Character := 'a' with Alignment => 8;
      X : Boolean with Size => 8, Import, Address => Z'Address; --  X might have invalid values, but it does not have unused bits
   begin
      null;
   end Test_Object_Size_Check_On_Source_6;

   type H_R2b is record
     C : R2b;
   end record;

   procedure Test_Object_Size_Check_On_Source_8 is
      X : H_R2b := (C => ('a', 'b', true));
      Y : R3
      with Import, Address => X.C'Address;  --  Should be rejected, X has unused bits
   begin
      null;
   end Test_Object_Size_Check_On_Source_8;
begin
   null;
end P;
