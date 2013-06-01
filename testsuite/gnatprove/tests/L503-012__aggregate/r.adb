procedure R is

   subtype Int5 is Integer range 1 .. 5;
   subtype Int6 is Integer range 1 .. 6;

   type Arr is array (Natural range <>) of Int5;

   subtype A26 is Arr (2 .. 6);

   type R is record
      F : A26;
   end record;

   type AR is array (Natural range <>) of R;

   subtype AR15 is AR (1 .. 5);

   procedure P1 (A : in out AR15; N : Integer)
     with Pre => (N in 1 .. 5);

   procedure P1 (A : in out AR15; N : Integer) is
   begin
      A := (others => (F => (2 => 1, others => A (N).F (N))));
   end P1;

   procedure P2 (A : in out AR15; N : Integer)
     with Pre => (N in 2 .. 6);

   procedure P2 (A : in out AR15; N : Integer) is
   begin
      A := (others => (F => (2 => 1, others => A (N).F (N))));
   end P2;

   type AA is array (Natural range <>) of A26;

   subtype AR37 is AA (3 .. 7);

   procedure P3 (A : in out AR37; N : Integer)
     with Pre => (N in 3 .. 4);

   procedure P3 (A : in out AR37; N : Integer) is
      I : Int6 := A (N)(N);
   begin
      A := (others => (3 => 1, others => A (N)(N)));
   end P3;

   procedure P4 (A : in out AR37; N : Integer)
     with Pre => (N in 2 .. 6);

   procedure P4 (A : in out AR37; N : Integer) is
      I : Int6 := A (N)(N);
   begin
      A := (others => (3 => 1, others => A (N)(N)));
   end P4;

begin
   null;
end R;
