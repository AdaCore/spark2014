with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

procedure Borrow is

   type Int is new Integer with Default_Value => 42;
   type Ptr is access all Int;
   type CPtr is access constant Int;

   procedure Free (P : in out Ptr)
   with
     Post => P = null,
     Import;

   type Rec is record
     C : Ptr;
     D : Ptr;
   end record;
   type RPtr is access Rec;
   type Arr is array (1 .. 10) of Rec;
   type Acc is access Arr;

   X : Ptr := new Int;
   Z : CPtr := new Int'(42);
begin
   declare
      Y : access constant Int := X;
   begin
      for J in 1 .. 10 loop
         pragma Assert (X.all = Y.all);
      end loop;
   end;

   Free (X);

   declare
      type Flat is record
         A : aliased Int;
         B : Ptr;
      end record;
      type Loc is access all Int;
      U : Flat := (0, new Int);
      V : Loc := U.A'Access;
      W1 : access constant Int := U.B;
      W2 : Int := U.A;
   begin
      null;
   end;

   declare
      A : RPtr := new Rec'(C => new Int, D => null);
      U : RPtr := A;
      V : access constant Int := A.C;
   begin
      null;
   end;

   declare
      Var : Ptr;
      War : Ptr;
      Bar : Ptr;

      function At_End_Borrow (E : access constant Int) return access constant Int is
         (E)
      with Ghost,
           Annotate => (GNATprove, At_End_Borrow);

      Y : access Int := Var;
      Z : access constant Int := War;

      function Ident (X : access Int; Y : Ptr) return access Int
        with Post =>
          At_End_Borrow (Ident'Result).all = At_End_Borrow (X).all
      is
         Cst1 : access constant Int := Y;
         Loc : access Int := X;
         Cst2 : access constant Int := Y;
         pragma Assert (At_End_Borrow (Loc).all = At_End_Borrow (X).all);
      begin
         return X;
      end;

      function Ident2 (X : access constant Int) return access constant Int
      is
         Loc : access constant Int := X;
      begin
         return X;
      end;

      YY : Ptr;
      A : access Int := Ident (Bar, YY);
   begin
      pragma Assert (At_End_Borrow (Y).all = At_End_Borrow (Var).all);
      pragma Assert (At_End_Borrow (A).all = At_End_Borrow (Bar).all);
   end;

   declare
      type T is delta 0.1 range 0.1 .. 1.0;
      subtype S is T delta 0.1 range 0.1 .. 1.0;
   begin
      null;
   end;

   declare
      type Pair is record
         A : Int;
         B : Int;
      end record;

      X : Pair := (0, 0);
      Y : Pair := X'Update (A => 42);

      type Arr is array (1 .. 2) of Int range 1 .. 2;
      T : Arr := (for I in 1 .. 2 => Int (I));
   begin
      for E : Int range 1 .. 2 of T loop
         pragma Assert (E in 1 .. 2);
      end loop;

      pragma Assert (for all E : Int range 1 .. 2 of T => E in 1 .. 2);
   end;

   declare
      package Lists is new Formal_Doubly_Linked_Lists (Integer);
      use Lists;
      L : List (10);
   begin
      for E : Integer range Integer'Range of L loop
         null;
      end loop;
   end;


end Borrow;
