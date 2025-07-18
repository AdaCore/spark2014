procedure C83E02A with SPARK_Mode is

   procedure P2 (A, B : Integer) is
      type T (MAX : Integer) is record
         VALUE : Integer range 1 .. 3;
      end record;
      X : T (A);
   begin
      X := (MAX => 4, VALUE => B); -- ( 4 , 3 )
   end P2;

begin
   P2 (4, 3);
end C83E02A;
