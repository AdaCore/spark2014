procedure Init with SPARK_Mode is

   type Ar is array (0 .. 1) of Integer;

   procedure P (X : out Ar; Status : out Boolean)
   with Relaxed_Initialization => X,
        Post => (if Status then X'Initialized);

   procedure P (X : out Ar; Status : out Boolean) is
   begin
      X (0) := 1;
      Status := False;
   end P;

   Z : Ar;
   B : Boolean;
begin
   loop
      P (Z, B);
      exit when B;
   end loop;
end Init;
