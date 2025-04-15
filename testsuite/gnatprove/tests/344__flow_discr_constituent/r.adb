procedure R (V : Integer)
  with Global => null
is

   --  Type with a discriminant

   type T (D : Integer) is record
      C : Integer;
   end record;

   --  Configuration procedure for a formal parameter of this type. Instead
   --  of calling this routine, this test inlines its contract and its body.

   procedure Configure (Y : out T)
      with Pre => Y.D = 0
   is
   begin
      Y := (D => 0, C => 0);
   end;

   --  Package with constituents of this type, which are configured
   --  using explicit and generated Global contracts.

   package Hidden with Abstract_State => (State_A, State_B) is
      procedure Initialize_A
         with Pre => True, Global => (Output => State_A);
      procedure Initialize_B
         with Pre => True;
   end;

   package body Hidden with Refined_State => (State_A => A, State_B => B) is

      A : T (V);
      B : T (V);

      procedure Initialize_A is
      begin
         pragma Assert (A.D = 0);
         A := (D => 0, C => 0);
      end;

      procedure Initialize_B is
      begin
         pragma Assert (B.D = 0);
         B := (D => 0, C => 0);
      end;
   end;

   --  Similar as above, but the constituent is implicitly lifted to a
   --  singleton abstract state.

   package Hidden_Implicit is
      procedure Initialize_C
         with Pre => True;
   end;

   package body Hidden_Implicit is

      C : T (V);

      procedure Initialize_C is
      begin
         pragma Assert (C.D = 0);
         C := (D => 0, C => 0);
      end;
   end;

   D : T (V);
   E : T (V);

   --  Finally, similar code, but for objects that are not constituents of
   --  an abstract state; here we have no data leaks, so the Global contract
   --  is right.

   procedure Initialize_D
     with Pre => True, Global => (Output => D) is
   begin
      pragma Assert (D.D = 0);
      D := (D => 0, C => 0);
   end;

   procedure Initialize_E
     with Pre => True is
   begin
      pragma Assert (E.D = 0);
      E := (D => 0, C => 0);
   end;

begin
   Hidden.Initialize_A;
   Hidden.Initialize_B;
   Hidden_Implicit.Initialize_C;
   Initialize_D;
   Initialize_E;
end;
