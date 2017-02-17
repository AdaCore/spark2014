package P
  with SPARK_Mode => On
is
   A : Integer := 1;
   B : Integer := 1;

   --  Formal Mode and Depends inconsistent
   procedure P1a (X : in Integer)
     with Depends => (X => X);

   --  Formal Mode and Depends inconsistent - same as P1a,
   --  but using +null on the right
   procedure P1b (X : in Integer)
     with Depends => (X => +null);



   --  Global Mode and Depends inconsistent
   procedure P2a
     with Global => (Input => A),
          Depends => (A => A);

   --  Global Mode and Depends inconsistent - same as P2a,
   --  but using +null on the right
   procedure P2b
     with Global => (Input => A),
          Depends => (A => +null);


   --  Formal Mode and Depends inconsistent.
   procedure P3a (X : out Integer)
     with Depends => (X => X);

   --  Formal Mode and Depends inconsistent, same as P3a,
   --  but using +null on the right
   procedure P3b (X : out Integer)
     with Depends => (X => +null);



   --  Global mode and Depends inconsistent.
   procedure P4a
     with Global => (Output => A),
          Depends => (A => A);

   --  Global mode and Depends inconsistent, same as P4a
   --  but using +null on the right
   procedure P4b
     with Global => (Output => A),
          Depends => (A => +null);



   --  Formal mode and Depends inconsistent
   procedure P5 (X : in out Integer)
     with Depends => (X => null);

   --  Global mode and Depends inconsistent
   procedure P6
     with Global => (In_Out => A),
          Depends => (A => null);

end P;
