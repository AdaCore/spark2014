package body Tagged_Discr with
  SPARK_Mode
is

   procedure Init (V : out T) is

   begin
      V := (Discr => A, Z => False, X => 0);
   end Init;

   procedure Update (V : in out T) is
   begin
      V.Z := False;
      case V.Discr is
         when A | C =>
            V.X := 0;
         when others =>
            V.Y := 0.0;
      end case;
   end Update;

   procedure Init (V : out U1) is
      pragma SPARK_Mode (Off);  --  tagged aggregate
   begin
     V := (T'(Discr => A, Z => False, X => 0) with W => 0);
   end Init;

   procedure Update (V : in out U1) is
   begin
      V.Z := False;
      case V.Discr is
         when A | C =>
            V.X := 0;
         when others =>
            V.Y := 0.0;
      end case;
      V.W := 0;
   end Update;

   procedure Init (V : out U2) is
      pragma SPARK_Mode (Off);  --  tagged aggregate
   begin
     V := (T'(Discr => A, Z => False, X => 0) with W => 0, XX => 0, YY => 0.0);
   end Init;

   procedure Update (V : in out U2) is
   begin
      Update (T(V));
      V.W := 0;
      V.XX := 0;
      V.YY := 0.0;
   end Update;

end Tagged_Discr;
