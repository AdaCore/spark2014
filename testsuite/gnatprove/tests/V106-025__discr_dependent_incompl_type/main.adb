procedure Main (X : Positive) with SPARK_Mode is
   type R1 (D1 : Integer);
   type R3 (D3 : Integer);

   type ACC_R1 is access R1;
   type ACC_R3 is access R3;

   type T is access Integer;

   type R1 (D1 : Integer) is record
      C1 : ACC_R3 (D1);
   end record;

   type R3 (D3 : Integer) is record
      C3 : T;
   end record;

   U : R1 (X) :=
     (D1 => X, C1 =>
         new R3'(D3 => X, C3 => new Integer'(14)));

   type R4 (D4 : Integer);
   type R2 (D2 : Integer);
   type Arr;

   type ACC_R2 is access R2;
   type ACC_R4 is access R4;
   type ACC_Arr is access Arr;

   type R4 (D4 : Integer) is record
      C4 : ACC_R2 (D4);
   end record;

   type Arr is array (Positive range <>) of ACC_R4;

   type R2 (D2 : Integer) is record
      C2 : ACC_Arr (1 .. D2);
   end record;

   V : R4 (X) :=
     (D4 => X, C4 =>
         new R2'(D2 => X, C2 =>
                      new Arr'(1 .. X =>
                                  new R4'(D4 => 0, C4 =>
                                             new R2'(D2 => 0, C2 =>
                                                        new Arr'(1 .. 0 => <>))))));
begin
   pragma Assert (if 2 <= X then V.C4.C2 (2).C4.C2'Length = 0);
end;
