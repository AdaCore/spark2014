package body Foo is

   procedure Sleep (N : Natural)
   with Global => null,
        Depends => (null => N),
        Import,
        Convention => C;

   procedure Test_01_E is
      My_A : array (1..20) of Integer;
      procedure Local is
      begin
         My_A (1) := 0;
      end Local;
   begin
      Local;
   end Test_01_E;

   procedure Test_02_E (R : out Boolean) is
      My_A : array (1..20) of Integer;
      procedure Local is
      begin
         My_A (1) := 0;
      end Local;
   begin
      Local;
      R := My_A (1) = 0;
   end Test_02_E;

   G1, G2 : Integer := 0;

   procedure Copy_Stuff (X, Y : out Integer) with
     Global  => (G1, G2),
     Depends => (X => G1,
                 Y => G2)
   is
   begin
      X := G1;
      Y := G2;
   end Copy_Stuff;

   procedure Test_03_E (A, B : out Integer) is
   begin
      Copy_Stuff (A, B);
      A := 5;
   end Test_03_E;

   procedure Test_04_E (A, B : out Integer) is
      procedure Set (N : Integer) with Global => (Output => (A, B))
      is
      begin
         A := N;
         B := N;
      end Set;
   begin
      Set (5);
      B := 8;
   end Test_04_E;

   procedure Test_05_Ok (A, B : out Integer) is
      procedure Set (N : Integer) with
         Global => (Input => A,
                    Output => B),
         Depends => (B    => N,
                     null => A)
      is
      begin
         Sleep (A);
         B := N;
      end Set;
   begin
      A := 1;
      Set (5);
   end Test_05_Ok;

   procedure Test_06_Ok (A, B : out Integer) is
      procedure Set (N : Integer) with
         Global => (Input => A,
                    Output => B)
      is
      begin
         Sleep (A);
         B := N;
      end Set;
   begin
      A := 1;
      Set (5);
   end Test_06_Ok;


end Foo;
