procedure Main is

   --  type with discriminant

   type T (D : Integer) is record
      C : Integer;
   end record;

   --  configuration procedure for a formal parameter of this type

   procedure Configure (Y : out T)
      with Pre => Y.D = 0
   is
   begin
      Y := (D => 0, C => 0);
   end;

   --  global objects of this type

   A : T (0);
   B : T (0);

   --  initialization procedure with explcit Global and generated Global

   procedure Initialize_A
      with Pre => True, Global => (Output => A)
   is
   begin
      Configure (A);
   end;

   procedure Initialize_B
      with Pre => True -- generated Global should be => (Output => B)
   is
   begin
      Configure (B);
   end;

begin
   Initialize_A;
   Initialize_B;
end;
