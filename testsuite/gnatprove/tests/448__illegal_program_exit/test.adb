procedure Test with SPARK_Mode is
   G : aliased Integer;

   procedure P (X : in out Integer) with
     Import,
     Always_Terminates,
     Global => null,
     Program_Exit => True;

   procedure P1 (X : in out Integer) with
     Import,
     Always_Terminates,
     Global => (In_Out => G),
     Program_Exit => True;

   procedure P2 (X : in out Integer) with
     Import,
     Always_Terminates,
     Global => (In_Out => G),
     Program_Exit => X'Old > 0;

   procedure P3 (X : in out Integer) with
     Import,
     Always_Terminates,
     Global => (In_Out => G),
     Program_Exit => G > 0;

   procedure P4 (X : aliased in out Integer) with
     Import,
     Always_Terminates,
     Global => null,
     Program_Exit => True;

   -- Program_Exit can be specified on a ghost subprogram

   procedure Bad_Ghost (X : in out Integer) with
     Ghost,
     Import,
     Program_Exit => True;

   --  Tool limitation: Program_Exit cannot be specified on a dispatching

   package Nested is
      type T is tagged null record;
      procedure Bad_Dispatch (X : in out T) with
        Import,
        Program_Exit => True;
   end Nested;

   --  Tool limitation: Outputs of the callee not mentioned in its Program_Exit
   --  postcondition might be left in an inconsistent state.

   procedure Bad_Call (X : in out Integer) with
     Program_Exit => G > 0
   is
   begin
      P4 (G);
   end Bad_Call;

   procedure Bad_Call_2 (X : in out Integer) with
     Program_Exit => G > 0
   is
   begin
      P2 (X);
   end Bad_Call_2;

   procedure OK_Call_1 (X : in out Integer) with
     Program_Exit => G'Old > 0
   is
   begin
      P (G);
   end OK_Call_1;

   procedure OK_Call_2 (X : aliased in out Integer) with
     Program_Exit => G > 0
   is
   begin
      P4 (X);
      P3 (X);
   end OK_Call_2;

   procedure OK_Call_3 (X : in out Integer) with
     Program_Exit => G > 0
   is
   begin
      P (G);
   end OK_Call_3;

   --  Tool limitation: 'Access on subprograms with Program_Exit

   procedure Bad_Access is
      type A is access procedure (X : in out Integer);
      C : A := P'Access;
   begin
      null;
   end Bad_Access;

   --  Restriction: Program_Exit should only mention outputs which are
   --  stand-alone objects.

   procedure Scope (F : in out Integer) is
      procedure OK_1 (X : in out Integer) with
        Import,
        Always_Terminates,
        Global => (In_Out => F),
        Program_Exit => True;

      procedure OK_2 (X : in out Integer) with
        Import,
        Always_Terminates,
        Global => (In_Out => F),
        Program_Exit => F'Old > 0;

      procedure Bad (X : in out Integer) with
        Import,
        Always_Terminates,
        Global => (In_Out => F),
        Program_Exit => F > 0;
   begin
      null;
   end Scope;
begin
   null;
end;
