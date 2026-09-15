pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_First, After_First   : Integer;
   Before_Second, After_Second : Integer;
   Output_First                : out Integer;
   Output_Second               : out Integer)
with
  SPARK_Mode,
  Depends =>
    (Output_First  => (Before_First, Before_Second),
     Output_Second => (Before_First, Before_Second),
     null          => (After_First, After_Second))
is
   type Pair is array (1 .. 2) of Integer;

   function Make_Pair (First, Second : Integer) return Pair
   with Depends => (Make_Pair'Result => (First, Second));

   function Make_Pair (First, Second : Integer) return Pair is
     (First, Second);

   First  : Integer := Before_First;
   Second : Integer := Before_Second;
   Saved  : Pair;

begin
   <<Capture>>
   First := After_First;
   Second := After_Second;
   Saved := Make_Pair (First, Second)'At (Capture);
   Output_First := Saved (1);
   Output_Second := Saved (2);
end Test;
