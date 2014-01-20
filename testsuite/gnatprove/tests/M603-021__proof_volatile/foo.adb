package body Foo
is

   V : Integer with Volatile, Async_Writers;

   type Volatile_Int is new Integer with Volatile;

   type T is range 1 .. 10;
   V2 : T with Volatile, Async_Writers;

   type Array_T is array (T) of Integer;

   V3 : Volatile_Int;

   type Rec_T is record
      X : Integer;
   end record;

   type Volatile_Rec_T is new Rec_T with Volatile;

   V4 : Volatile_Rec_T with Volatile, Async_Writers;

   procedure Test_01 (X, Y : out Integer)
     with Post => X = Y -- not provable
   is
   begin
      X := V;
      Y := V;
      V := 88;
   end Test_01;

   --  procedure Test_02 (N    : in out Volatile_Int;
   --                     X, Y :    out Integer)
   --    with Post => X = Y -- not provable
   --  is
   --  begin
   --     X := Integer (N);
   --     Y := Integer (N);
   --  end Test_02;

   --  procedure Test_03 (N    : in     Volatile_Int;
   --                     X, Y :    out Integer)
   --    with Post => X = Y -- not provable
   --  is
   --  begin
   --     X := Integer (N);
   --     Y := Integer (N);
   --  end Test_03;

   procedure Read_Vol_IO (A : in out Volatile_Rec_T;
                          B :    out Integer)
   is
      Tmp : Rec_T := Rec_T (A);
   begin
      B := A.X;
   end Read_Vol_IO;

   procedure Use_Read_Vol_IO (B :    out Integer;
                              C :    out Integer)
   with Post => B = C -- not provable
   is
   begin
      Read_Vol_IO (V4, B);
      Read_Vol_IO (V4, C);
   end Use_Read_Vol_IO;

   procedure Read_Vol_I (A : in     Volatile_Rec_T;
                         B :    out Integer)
   is
      Tmp : Rec_T := Rec_T (A);
   begin
      B := Tmp.X;
   end Read_Vol_I;

   procedure Use_Read_Vol_I (B :    out Integer;
                             C :    out Integer)
   with Post => B = C -- not provable
   is
   begin
      Read_Vol_I (V4, B);
      Read_Vol_I (V4, C);
   end Use_Read_Vol_I;

   procedure Use_Read_Vol_I2 (A : in     Volatile_Rec_T;
                              B :    out Integer;
                              C :    out Integer)
   with Post => B = C -- not provable
   is
   begin
      Read_Vol_I (A, B);
      Read_Vol_I (A, C);
   end Use_Read_Vol_I2;

end Foo;
