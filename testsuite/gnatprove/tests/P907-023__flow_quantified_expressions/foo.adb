package body Foo is

   type T is array (Positive range <>) of Boolean;
   type R is record
      X : Boolean;
   end record;
   type CT is array (1 .. 10) of R;

   function F (N : Integer) return Boolean is (N = 42);

   procedure Test_01 (A : Integer;
                      B : out Boolean)
   with Global  => null,
        Depends => (B => A),
        Post    => B = (for all J in Integer range 1 .. A => J - 1 < J)
   is
   begin
      B := (for all I in Integer range 1 .. A => I - 1 < I);
   end Test_01;

   procedure Test_02 (A : Integer;
                      B : out Boolean)
   with Global  => null,
        Depends => (B => A),
        Post    => B = (for all J in 1 .. A => J - 1 < J)
   is
   begin
      B := (for all I in 1 .. A => I - 1 < I);
   end Test_02;

   procedure Test_03 (A : T;
                      B : out Boolean)
   with Global  => null,
        Depends => (B => A),
        Post    => B = (for all J in A'Range => J - 1 < J)
   is
   begin
      B := (for all I in A'Range => I - 1 < I);
   end Test_03;

   procedure Test_04 (A : Integer;
                      B : out Boolean)
   with Global  => null,
        Depends => (B => A),
        Post    => B = (for all J in Integer range 1 .. A => F (J))
   is
   begin
      B := (for all I in Integer range 1 .. A => F (I));
   end Test_04;

   procedure Test_05 (A: in out CT)
   with Global => null,
        Post   => (for all N in A'Range => A (N).X)
   is
   begin
      for I in A'Range loop
         A (I).X := A (I).X or not A (I).X;
         pragma Loop_Invariant (for all J in A'First .. I => A (J).X);
      end loop;
   end Test_05;

end Foo;
