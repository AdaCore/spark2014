procedure Init with SPARK_Mode is

   type Ar is array (0 .. 1) of Integer;

   type Rec is record
      A, B, C : Integer;
   end record;

   procedure P (X : out Ar; Status : out Boolean) is
   begin
      X (0) := 1;
      Status := False;
   end P;

   procedure Q (X : out Integer; Status : Boolean) is
   begin
      if Status then
         X := 24;
      else
         null;
      end if;
   end Q;

   procedure R (X : out Rec) is
   begin
      X.A := 1;
   end R;

   procedure S (X : out Rec; Status : Boolean) is
   begin
      if Status then
         X.A := 24;
      else
         null;
      end if;
   end S;

begin
   null;
end Init;
