package body Classwide with
  SPARK_Mode
is

   procedure C_Init (V : out T_Class) is
   begin
      Init (V);
   end C_Init;

   procedure Init (V : out T) is
      pragma SPARK_Mode (Off);  --  tagged aggregate
   begin
      V := (Z => False, X => 0, Y => 0.0);
   end Init;

   procedure D_Init (V : out T) is
   begin
      C_Init (T'Class (V));
   end D_Init;

   procedure C_Update (V : in out T2_Class) is
   begin
      Update (V);
   end C_Update;

   procedure Update (V : in out T) is
   begin
      V.Z := False;
      V.X := 0;
      V.Y := 0.0;
   end Update;

   procedure D_Update (V : in out T) is
   begin
      C_Update (T'Class (V));
   end D_Update;

   procedure Init (V : out U1) is
      pragma SPARK_Mode (Off);  --  tagged aggregate
   begin
      V := (T'(Z => False, X => 0, Y => 0.0) with null record);
   end Init;

   procedure Update (V : in out U1) is
   begin
      V.Z := False;
      V.X := 0;
      V.Y := 0.0;
   end Update;

   procedure Init (V : out U2) is
      pragma SPARK_Mode (Off);  --  tagged aggregate
   begin
     V := (T'(Z => False, X => 0, Y => 0.0) with W => 0, XX => 0, YY => 0.0);
   end Init;

   procedure Update (V : in out U2) is
   begin
      Update (T(V));
      V.W := 0;
      V.XX := 0;
      V.YY := 0.0;
   end Update;

end Classwide;
