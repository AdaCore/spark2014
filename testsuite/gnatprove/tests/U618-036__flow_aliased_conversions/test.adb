with Types; use Types;
with Ada.Unchecked_Conversion;

procedure Test with SPARK_Mode => On is
   Rec1 : Root_T := Constructor (1);
   Rec2 : Root_T := Constructor (2);
   Rec3 : Derived_T := Constructor (3);
   Glob1 : Derived_T := Constructor (4);

   procedure Stuff (A : in     Integer;
                    B : in out Root_T;
                    C :    out Root_T)
     with Global => (In_Out => Glob1)
   is
   begin
      Glob1.A := A;
      if B.Field < A then
         Foo (B);
      end if;
      C := Constructor (B.Field);
   end Stuff;

   procedure Stuff2 (A : in     Integer;
                     B : in out Integer;
                     C :    out Root_T)
   is
   begin
      if B < A then
         B := B + 1;
      end if;
      C := Constructor (B);
   end Stuff2;

   type Outer_T is record
      D : Root_T;
   end record;

   A : Outer_T := (D => Rec1);

   function UncF1 is new Ada.Unchecked_Conversion (Outer_T, Outer_T);

   procedure Stuff3 (A : in     Root_T;
                     B :    out Root_T)
   is
   begin
      B.Field := A.Field + 1;
   end Stuff3;

   type Inner is record
      C : Integer;
   end record;

   type Outer is record
      D : Inner;
   end record;

   function Conv is new Ada.Unchecked_Conversion (Outer, Outer);

   procedure Stuff4 (X : Inner;
                     Y : out Inner) is
   begin
      Y := X;
   end;

   Z : Outer := (D => (C => 0));
begin
   Stuff (A => Rec1.Field,
          B => Rec1,  -- Not aliased with param A; passed by copy
          C => Rec2);
   Stuff (A => 6,
          B => Rec1,
          C => Root_T (Rec3)); -- No aliasing

   Stuff (A => 6,
          B => Rec1,
          C => Root_T (Glob1)); -- Aliased with global

   Stuff2 (A => 6,
           B => Root_T (Glob1).Field, -- Aliased formal parameters
           C => Root_T (Glob1));

   Stuff3 (A => Rec1,  -- Basic-case alias (due to pass-by-reference)
           B => Rec1);

   Stuff3 (A => A.D,  --  Another basic-case alias
           B => A.D);

   Stuff4 (X => Conv (Z).D,  --  Aliased, with an unchecked conversion
           Y => Z.D);

   Stuff3 (A => UncF1(A).D, --  Aliased, with an unchecked conversion
           B => A.D);       --  of tagged type.

   Stuff2 (A => UncF1(A).D.Field, --  Similar to previous, but Field is passed
           B => A.D.Field,        --  by-copy so not aliased
           C => Rec2);

end Test;
