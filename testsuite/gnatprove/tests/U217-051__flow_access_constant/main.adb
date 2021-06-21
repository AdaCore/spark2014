procedure Main with SPARK_Mode is
   type AV is access Integer;
   type AS is access procedure;

   A : constant AV := null;
   B : constant AS := null;
   C : constant Integer := 0;

   package P
     with Initializes => (Y => (A, B, C)),
          Initial_Condition => Y
   is
      Y : Boolean := A = null and B = null and C = 0;
   end;

   procedure Proc (Y : out Boolean)
     with Depends => (Y => (A, B, C)), Post => Y
   is
   begin
      Y := A = null and B = null and C = 0;
   end;

begin
   null;
end;
