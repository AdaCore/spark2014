pragma Spark_Mode (On);

procedure Root is

   generic
      type T is private;
      C : T;
   procedure Generic_P (R : out T);

   procedure Generic_P (R : out T) is
   begin
      R := C;
   end Generic_P;

   type Int_Array is array (Natural range <>) of Integer;

   procedure P1 (N : Integer; O : out Integer)
   is
      subtype N_Array is Int_Array (0 .. N);

      procedure P2 is new Generic_P (
         T => N_Array,
         C => [others => 0]
      );

      A : N_Array;
   begin
      P2 (A); O := N;
   end P1;

   O : Integer;
begin
   P1 (4, O);
end;
