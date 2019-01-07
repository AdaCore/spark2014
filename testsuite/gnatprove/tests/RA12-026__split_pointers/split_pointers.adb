procedure Split_Pointers with SPARK_Mode is
   type Int_Ptr is access Integer;

   X : constant int_ptr := null;
   Y : int_ptr := null;
   Z : int_ptr;
   W : int_ptr := new Integer'(10);
   CC : int_ptr := new Integer'(10);
   C : access constant Integer := CC;
   DD : int_ptr := new Integer'(10);
   D : constant access constant Integer := DD;

   procedure Test_In (X : int_ptr; Y : access Integer; Z : access constant Integer) with
     Pre => True
   is
      Tmp : Integer;
   begin
      if Z /= null and X /= null and Y /= null then
         Tmp := X.all;
         X.all := Y.all;
         Y.all := Tmp;
      end if;
   end Test_In;

   procedure Test_In_Out (X : in out int_ptr; Y : in out int_ptr; Z : in out int_ptr) with
     Pre => True
   is
   begin
      if Z /= null then
         X := Y;
         Y := X;
      end if;
      Z := null;
   end Test_In_Out;

   procedure Test_Glob with
     Pre => True,
     Global => (Input  => (C, W),
                In_Out => Y,
                Output => Z)
   is
   begin
      if C /= null and Y /= null and W /= null then
         Y.all := W.all;
      end if;
      Z := null;
   end Test_Glob;

   function Test_Fun (X : int_ptr; Y : access Integer; Z : access constant Integer)  return Integer with
     Global => (C, W),
     Pre => True
   is
      Tmp : Integer := 0;
   begin
      if Z /= null and X /= null and Y /= null and C /= null and W /= null then
         Tmp := X.all;
         Tmp := Tmp + Y.all;
      end if;
      return Tmp;
   end Test_Fun;


   type Holder is record
      X : Int_Ptr;
   end record;

   H1 : Holder;
   H2 : constant Holder := (X => new Integer'(10));
   H3 : Holder := (X => new Integer'(10));
   H4 : Holder := (X => null);
   T  : Integer;
begin
   Test_In (X, Y, C);
   T := Test_Fun (X, Y, C);
   Test_In_Out (W, Y, Z);
   Test_In (H1.X, H3.X, H2.X);
   T := Test_Fun (H1.X, H3.X, H2.X);
   Test_In_Out (H1.X, H3.X, H4.X);
   Test_Glob;
end;
