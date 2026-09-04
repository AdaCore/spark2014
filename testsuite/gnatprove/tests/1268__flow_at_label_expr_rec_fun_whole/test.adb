pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_Left, After_Left   : Integer;
   Before_Right, After_Right : Integer;
   Output_Left               : out Integer;
   Output_Right              : out Integer)
with
  SPARK_Mode,
  Depends =>
    (Output_Left  => (Before_Left, Before_Right),
     Output_Right => (Before_Left, Before_Right),
     null         => (After_Left, After_Right))
is
   type Pair is record
      Left  : Integer;
      Right : Integer;
   end record;

   function Make_Pair (Left, Right : Integer) return Pair
   with Depends => (Make_Pair'Result => (Left, Right));

   function Make_Pair (Left, Right : Integer) return Pair is
     (Left => Left, Right => Right);

   Left  : Integer := Before_Left;
   Right : Integer := Before_Right;
   Saved : Pair;

begin
   <<Capture>>
   Left := After_Left;
   Right := After_Right;
   Saved := Make_Pair (Left, Right)'At (Capture);
   Output_Left := Saved.Left;
   Output_Right := Saved.Right;
end Test;
